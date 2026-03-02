#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# This script builds libyices2j.so.

# INFO: Before running this script, you need to do build Yices2.
# See the corresponding section in doc/Developers.md for details.

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

YICES_HEADER_DIR="$1"/include
YICES_LIB_DIR="$1"/lib

GMP_HEADER_DIR="$2"/include
GMP_LIB_DIR="$2"/lib

POLY_LIB_DIR="$3"/lib
CUDD_LIB_DIR="$4"/lib

# check requirements
if [ ! -f "$YICES_LIB_DIR/libyices.a" ]; then
    echo "You need to specify the directory with the downloaded and compiled Yices on the command line!"
    echo "Can not find $YICES_LIB_DIR/libyices.a"
	exit 1
fi
if [ ! -f "$GMP_LIB_DIR/libgmp.a" ]; then
    echo "You need to specify the GMP directory on the command line!"
    echo "Can not find $GMP_LIB_DIR/libgmp.a"
    exit 1
fi
if [ ! -f "$POLY_LIB_DIR/libpoly.a" ]; then
    echo "You need to specify the Libpoly directory on the command line!"
    echo "Can not find $POLY_LIB_DIR/libpoly.a"
    exit 1
fi
if [ ! -f "$CUDD_LIB_DIR/libcudd.a" ]; then
    echo "You need to specify the CUDD directory on the command line!"
    echo "Can not find $CUDD_LIB_DIR/libcudd.a"
    exit 1
fi

SRC_FILES="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c"
OBJ_FILES="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.o"

OUT_FILE="libyices2j.so"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the Yices header files
gcc -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter \
    $JNI_HEADERS -I$YICES_HEADER_DIR -I$GMP_HEADER_DIR $SRC_FILES -fPIC -c

echo "Compilation Done"
echo "Linking libraries together into one file..."

# This will link together the file produced above, the Yices library, the GMP library and the standard libraries.
# Everything except the standard libraries is included statically.
# The result is a single shared library containing all necessary components.
gcc -Wall -g -o $OUT_FILE -shared -Wl,-soname,libyices2j.so \
    -L$YICES_LIB_DIR -L$GMP_LIB_DIR -L$POLY_LIB_DIR -L$CUDD_LIB_DIR \
    -I$GMP_HEADER_DIR $OBJ_FILES -Wl,-Bstatic \
    -lyices -lcudd -lpoly -lgmpxx -lgmp -static-libstdc++ -lstdc++ \
    -Wl,-Bdynamic -lc -lm -Wl,--version-script=libyices2j.version


if [ $? -ne 0 ]; then
    echo "There was a problem during compilation of \"org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c\""
    exit 1
fi

echo "Linking Done"
echo "Reducing file size by dropping unused symbols..."

strip ${OUT_FILE}

echo "Reduction Done"

MISSING_SYMBOLS="$(readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND)"
if [ ! -z "$MISSING_SYMBOLS" ]; then
    echo "Warning: There are the following unresolved dependencies in libyices2j.so:"
    readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND
    exit 1
fi

echo "All Done"
