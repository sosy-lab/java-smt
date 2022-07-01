#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# #########################################
#
# INFO:
# This script is automatically called from ant when publishing MathSAT5 or OptiMathSAT.
# There is no need to call this scripts manually, except for developing and debugging.
#
# #########################################

# This script builds either libmathsat5j.so (bindings to mathsat5), or
# liboptimathsat5j.so (bindings to optimathsat5).
# In future, mathsat5 and optimathsat should merge, making the switching obsolete.

# For building libmathsat5j.so, there are two dependencies:
# - The static Mathsat5 library as can be downloaded from http://mathsat.fbk.eu/download.html
# - The static GMP library compiled with the "-fPIC" option.
#   To create this, download GMP 6.1.2 from http://gmplib.org/ and run
#     ./configure --enable-cxx --with-pic --disable-shared --enable-fat
#     make

# For building liboptimathsat5.so, OptiMathSat5 can be downloaded from
# http://optimathsat.disi.unitn.it/.

# To build mathsat bindings: ./compile.sh $MATHSAT_DIR $GMP_DIR
# To build optimathsat bindings: ./compile.sh $MATHSAT_DIR $GMP_DIR -optimathsat

# This script searches for all included libraries in the current directory first.
# You can use this to override specific libraries installed on your system.
# You can also use this to force static linking of a specific library,
# if you put only the corresponding .a file in this directory, not the .so file.

# For example, to statically link against libstdc++,
# compile this library with --with-pic,
# and put the resulting libstdc++.a file in this directory.

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

JNI_HEADERS="$(../get_jni_headers.sh)"

MSAT_SRC_DIR="$1"/include
MSAT_LIB_DIR="$1"/lib
GMP_LIB_DIR="$2"/.libs
GMP_HEADER_DIR="$2"

SRC_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c"
OBJ_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.o"

# check requirements
if [ ! -f "$MSAT_LIB_DIR/libmathsat.a" ]; then
    echo "You need to specify the directory with the downloaded MathSAT5 on the command line!"
    exit 1
fi
if [ ! -f "$GMP_LIB_DIR/libgmp.a" ]; then
    echo "You need to specify the GMP directory on the command line!"
    echo "Can not find $GMP_LIB_DIR/libgmp.a"
    exit 1
fi

# switch between MathSAT5 and OptiMathSAT
if [ "$3" = "-optimathsat" ]; then
    echo "Compiling bindings to OptiMathSAT"
    SRC_FILES="$SRC_FILES optimization.c"
    OBJ_FILES="$OBJ_FILES optimization.o"
    OUT_FILE="liboptimathsat5j.so"
    ADDITIONAL_FLAGS="-D INCLUDE_OPTIMATHSAT5_HEADER"
else
    OUT_FILE="libmathsat5j.so"
    ADDITIONAL_FLAGS=""
fi

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the Mathsat header files
gcc -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter $JNI_HEADERS -I$MSAT_SRC_DIR -I$GMP_HEADER_DIR $SRC_FILES -fPIC -c $ADDITIONAL_FLAGS

echo "Compilation Done"
echo "Linking libraries together into one file..."

# This will link together the file produced above, the Mathsat library, the GMP library and the standard libraries.
# Everything except the standard libraries is included statically.
# The result is a single shared library containing all necessary components.
if [ `uname -m` = "x86_64" ]; then
    gcc -Wall -g -o ${OUT_FILE} -shared -Wl,-soname,libmathsat5j.so -L. -L${MSAT_LIB_DIR} -L${GMP_LIB_DIR} -I${GMP_HEADER_DIR} ${OBJ_FILES} -Wl,-Bstatic -lmathsat -lgmpxx -lgmp -static-libstdc++ -lstdc++ -Wl,-Bdynamic -lc -lm
else
    # TODO compiling for/on a 32bit system was not done for quite a long time. We should drop it.
    gcc -Wall -g -o ${OUT_FILE} -shared -Wl,-soname,libmathsat5j.so -L${MSAT_LIB_DIR} -L${GMP_LIB_DIR} -I${GMP_HEADER_DIR} ${OBJ_FILES} -Wl,-Bstatic -lmathsat -lgmpxx -lgmp -Wl,-Bdynamic -lc -lm -lstdc++
fi

if [ $? -ne 0 ]; then
    echo "There was a problem during compilation of \"org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c\""
    exit 1
fi

echo "Linking Done"
echo "Reducing file size by dropping unused symbols..."

strip ${OUT_FILE}

echo "Reduction Done"

MISSING_SYMBOLS="$(readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND)"
if [ ! -z "$MISSING_SYMBOLS" ]; then
    echo "Warning: There are the following unresolved dependencies in libmathsat5j.so:"
    readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND
    exit 1
fi

echo "All Done"
echo "Please check the following dependencies that will be required at runtime by mathsat5j.so:"
LANG=C objdump -p ${OUT_FILE} | grep -A50 "required from"
