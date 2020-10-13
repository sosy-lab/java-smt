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

# For building libmathsat5j.dll on Linux for Windows, there are the following dependencies:
# - The Mathsat5 library for Windows64 as can be downloaded from http://mathsat.fbk.eu/download.html
# - The static GMP library compiled with the "-fPIC" option.
#   To create this, download GMP from http://gmplib.org/ and run
#     ./configure --enable-cxx --with-pic --disable-shared --enable-fat --host=x86_64-w64-mingw32
#     make
#   TODO: MathSAT5 is linked against MPIR which aims to be compatible to GMP.
#   Perhaps, we should also use MPIR.
# - The Windows JNI headers in a reasonable LTS version:
#   Download the zip archive from https://jdk.java.net/ and unpack it
#   (e.g., https://download.java.net/openjdk/jdk11/ri/openjdk-11+28_windows-x64_bin.zip).

# To build mathsat bindings: ./compileForWindows.sh $MATHSAT_DIR $GMP_DIR $JNI_DIR

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

JNI_DIR="$3"/include
JNI_HEADERS="-I${JNI_DIR}/ -I${JNI_DIR}/win32/"

MSAT_SRC_DIR="$1"/include
MSAT_LIB_DIR="$1"/lib
MSAT_BIN_DIR="$1"/bin

MPIR_HEADER_DIR="$2"
MPIR_LIB_DIR="$2"/.libs
MPIR_INCLUDE_DIR="$2"

SRC_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c versions.c"
OBJ_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.o"

# check requirements
if [ ! -f "$MSAT_LIB_DIR/mathsat.dll" ]; then
    echo "You need to specify the directory with the downloaded Mathsat on the command line!"
    echo "Can not find $MSAT_LIB_DIR/mathsat.dll"
    exit 1
fi
if [ ! -f "$JNI_DIR/jni.h" ]; then
    echo "You need to specify the directory with the downloaded JNI headers on the command line!"
    echo "Can not find $JNI_DIR/jni.h"
    exit 1
fi

OUT_FILE="mathsat5j.dll"
BASIC_OPTIONS="-m64 -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the Mathsat header files
x86_64-w64-mingw32-gcc -g -o $OUT_FILE -shared -Wl,-soname,$OUT_FILE \
    -D_JNI_IMPLEMENTATION_ -Wl,--kill-at $JNI_HEADERS \
    -I$MSAT_SRC_DIR -I$MPIR_INCLUDE_DIR -L$MSAT_LIB_DIR \
    org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c \
    -lmathsat $MSAT_BIN_DIR/mpir.dll -lstdc++ -lpsapi 2>&1

echo "Compilation Done"
echo "Reducing file size by dropping unused symbols..."

strip ${OUT_FILE}

echo "Reduction Done"
echo "All Done"

echo "Please check the following dependencies that will be required at runtime by $OUT_FILE:"
echo "(DLLs like 'kernel32' and 'msvcrt' are provided by Windows)"
objdump -p $OUT_FILE | grep "DLL Name"
