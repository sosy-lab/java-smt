#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# #########################################
#
# INFO:
# This script is automatically called from ant when publishing MathSAT5.
# There is no need to call this scripts manually, except for developing and debugging.
#
# #########################################

# This script cross-compiles the MathSAT5 library `mathsat5j.dll` on a Linux host for a Windows64 target.
# There are the following dependencies:
# - MinGW (install Ubuntu package: `mingw-w64`)
# - The MathSAT5 library for Windows64 as can be downloaded from http://mathsat.fbk.eu/download.html
# - MathSAT5 is linked against GMP. We use the precompiled `gmp.dll` from the MathSAT5 archive.
#   Previously, MathSAT5 used MPIR which aimed to be compatible to GMP.
#   Since 2017, MPIR was no longer developed, and since 2022, MPIR officially dead.
#   When compiling our bindings, we use the header files from GMP.
#   We do not actually need to compile it. However, this is a nice test, whether our build system works as expected.
#   To build GMP, download GMP 6.3.0 from http://gmplib.org/ and run
#     ./configure --enable-cxx --with-pic --enable-shared --disable-static --enable-fat --host=x86_64-w64-mingw32
#     make -j4
# - The Windows JNI headers in a reasonable LTS version:
#   Download the zip archive from https://jdk.java.net/ and unpack it
#   (e.g., https://download.java.net/java/GA/jdk17.0.2/dfd4a8d0985749f896bed50d7138ee7f/8/GPL/openjdk-17.0.2_windows-x64_bin.zip).
#
# To build MathSAT5 bindings: ./compileForWindows-x64.sh $MATHSAT_DIR $GMP_DIR $JNI_DIR

check_requirements() {
    local file_path=$1
    local message=$2

    if [ ! -f "$file_path" ]; then
        echo "$message"
        echo "Cannot find $file_path"
        exit 1
    fi
}

set -e

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

OUT_FILE="mathsat5j.dll"

CC=x86_64-w64-mingw32-gcc
STRIP=strip

JNI_DIR="$3"/include
JNI_HEADERS="-I${JNI_DIR}/ -I${JNI_DIR}/win32/"

MSAT_SRC_DIR="$1"/include
MSAT_LIB_DIR="$1"/lib
MSAT_BIN_DIR="$1"/bin

GMP_DIR="$2"
GMP_LIB_DIR="$2/.libs"

SRC_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c"
OBJ_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.o"

check_requirements "$MSAT_LIB_DIR/mathsat.dll" "You need to specify the directory with the downloaded MathSAT5 on the command line!"
check_requirements "$JNI_DIR/jni.h" "You need to specify the directory with the downloaded JNI headers on the command line!"
check_requirements "$GMP_DIR/gmp.h" "You need to specify the directory with the downloaded GMP on the command line!"

rm "$OBJ_FILES"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the MathSAT5 header files
$CC -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter \
    -o $OUT_FILE -shared -Wl,-soname,$OUT_FILE \
    -D_JNI_IMPLEMENTATION_ -Wl,--kill-at \
    $JNI_HEADERS -I$MSAT_SRC_DIR -I$GMP_DIR -L$MSAT_LIB_DIR $SRC_FILES \
    -lmathsat $MSAT_BIN_DIR/gmp.dll -lstdc++ -lpsapi

echo "Compilation Done"
echo "Reducing file size by dropping unused symbols..."

$STRIP ${OUT_FILE}

echo "Reduction Done"
echo "All Done"

echo "Please check the following dependencies that will be required at runtime by $OUT_FILE:"
echo "(DLLs like 'kernel32' and 'msvcrt' are provided by Windows)"
objdump -p $OUT_FILE | grep "DLL Name"
