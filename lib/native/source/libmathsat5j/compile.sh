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

if [ "$(uname)" = "Darwin" ]; then
    IS_MACOS=true
else
    IS_MACOS=false
fi

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

if [ "$IS_MACOS" = true ]; then
    if ! command -v clang &> /dev/null; then
        echo "clang compiler not found."
        echo "Please install Apple's clang through the Xcode developer tools:"
        echo "    xcode-select --install"
        exit 1
    elif ! clang --version | grep -q "^Apple"; then
        echo "WARNING: clang compiler found but it is not Apple clang."
        echo "         This may cause problems with signing the library for use on macOS."
        echo "         Please install Apple's clang through the Xcode developer tools:"
        echo "             xcode-select --install"
    fi
fi

# switch between MathSAT5 and OptiMathSAT
if [ "$3" = "-optimathsat" ]; then
    echo "Compiling bindings to OptiMathSAT"
    SRC_FILES="$SRC_FILES optimization.c"
    OBJ_FILES="$OBJ_FILES optimization.o"
    OUT_FILE="liboptimathsat5j.so"
    ADDITIONAL_FLAGS="-D BUILD_FOR_OPTIMATHSAT5"
else
    if [ "$IS_MACOS" = true ]; then
        OUT_FILE="libmathsat5j.dylib"
    else
        OUT_FILE="libmathsat5j.so"
    fi
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
if [ "$IS_MACOS" = true ]; then
    # Next to some smaller macOS-specific changes compared to the Linux version,
    # there is one important peculiarity: Apple's clang does not support the `-Bstatic` flag
    # for an individual link. The Apple-specific counterpart `-static` has different behavior:
    # If specified, it does not only link the next library statically, but all libraries.
    # We do not want this, so we explicitly specify the path to the static libraries
    # where we want this (without `-l`).
    clang -Wall -g -o "${OUT_FILE}" -dynamiclib -Wl,-install_name,@rpath/libmathsat5j.dylib -L. -L"${MSAT_LIB_DIR}" -L"${GMP_LIB_DIR}" -I"${GMP_HEADER_DIR}" ${OBJ_FILES} "${MSAT_LIB_DIR}"/libmathsat.a -lgmpxx -lgmp -lstdc++ -lc -lm

elif [ "$(uname -m)" = "x86_64" ]; then
    gcc -Wall -g -o "${OUT_FILE}" -shared -Wl,-soname,libmathsat5j.so -L. -L"${MSAT_LIB_DIR}" -L"${GMP_LIB_DIR}" -I"${GMP_HEADER_DIR}" ${OBJ_FILES} -Wl,-Bstatic -lmathsat -lgmpxx -lgmp -static-libstdc++ -lstdc++ -Wl,-Bdynamic -lc -lm
else
    # TODO compiling for/on a 32bit system was not done for quite a long time. We should drop it.
    gcc -Wall -g -o "${OUT_FILE}" -shared -Wl,-soname,libmathsat5j.so -L"${MSAT_LIB_DIR}" -L"${GMP_LIB_DIR}" -I"${GMP_HEADER_DIR}" ${OBJ_FILES} -Wl,-Bstatic -lmathsat -lgmpxx -lgmp -Wl,-Bdynamic -lc -lm -lstdc++
fi

if [ $? -ne 0 ]; then
    echo "There was a problem during compilation of \"org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c\""
    exit 1
fi

echo "Linking Done"
echo "Reducing file size by dropping unused symbols..."

strip ${OUT_FILE}

echo "Reduction Done"

if [ "$IS_MACOS" = true ]; then
    # TODO: Be nice and also check for missing symbols
    echo -n ""
else
    MISSING_SYMBOLS="$(readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND)"
    if [ -n "$MISSING_SYMBOLS" ]; then
        echo "Warning: There are the following unresolved dependencies in libmathsat5j.so:"
        readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND
        exit 1
    fi
fi
echo "All Done"
echo "Please check the following dependencies that will be required at runtime by mathsat5j.so:"
LANG=C objdump -p ${OUT_FILE} | grep -A50 "required from"

if [ "$IS_MACOS" = true ]; then
    echo "
You've just built ${OUT_FILE} for macOS. Before you can use this library, you
need to sign it with a certificate that your system trusts, or with an Apple
Developer ID. Signing with a known, trusted certificate can be done with
this command:
    codesign -s \"Your Certificate Name\" --timestamp ${OUT_FILE}"
fi
