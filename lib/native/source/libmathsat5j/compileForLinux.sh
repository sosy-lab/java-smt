#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# #########################################
#
# INFO:
# This script is automatically called from ant when publishing MathSAT5.
# There is no need to call this script manually, except for developing and debugging.
#
# #########################################

# This script builds libmathsat5j.so (bindings to mathsat5).
# For building libmathsat5j.so, there are two dependencies:
# - The static Mathsat5 library as can be downloaded from http://mathsat.fbk.eu/download.html
# - The static GMP library compiled with the "-fPIC" option.
#   To create this, download GMP 6.3.0 from http://gmplib.org/ and build GMP:
#   For linux-x64:
#       ./configure --enable-cxx --with-pic --disable-shared --enable-static --enable-fat
#       make -j4
#   For linux-arm64:
#       ./configure --enable-cxx --with-pic --disable-shared --enable-static --enable-fat \
#            --host=aarch64-linux-gnu \
#            CC=aarch64-linux-gnu-gcc CXX=aarch64-linux-gnu-g++ LD=aarch64-linux-gnu-ld
#       make -j4
# - For linux-arm64: Provide JNI headers in a reasonable LTS version:
#   Download the zip archive from https://jdk.java.net/ and unpack it
#   (e.g., https://download.java.net/java/GA/jdk17.0.2/dfd4a8d0985749f896bed50d7138ee7f/8/GPL/openjdk-17.0.2_linux-aarch64_bin.tar.gz).
#
# This script searches for all included libraries in the current directory first.
# You can use this to override specific libraries installed on your system.
# You can also use this to force static linking of a specific library,
# if you put only the corresponding .a file in this directory, not the .so file.
# For example, to statically link against libstdc++,
# compile this library with --with-pic,
# and put the resulting libstdc++.a file in this directory.

# #########################################
# Usage: ./compileForLinux.sh <ARCH> <MATHSAT_DIR> <GMP_DIR> [<JNI_DIR>]
# ARCH should be either 'linux-x64' or 'linux-arm64'.
# JNI_DIR is not required for 'linux-x64'.

check_requirements() {
    local file_path=$1
    local message=$2

    if [ ! -f "$file_path" ]; then
        echo "$message"
        echo "Cannot find $file_path"
        exit 1
    fi
}

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

# Determine architecture and set variables accordingly
ARCH=$1
if [ "$ARCH" == "linux-x64" ]; then
    OUT_FILE="libmathsat5j-x64.so"
    CC=gcc
    STRIP=strip
    JNI_HEADERS="$(../get_jni_headers.sh)"
elif [ "$ARCH" == "linux-arm64" ]; then
    OUT_FILE="libmathsat5j-arm64.so"
    CC=aarch64-linux-gnu-gcc
    STRIP=aarch64-linux-gnu-strip
    JNI_DIR="$4/include"
    JNI_HEADERS="-I${JNI_DIR}/ -I${JNI_DIR}/linux/"
else
    echo "Invalid architecture specified. Use 'linux-x64' or 'linux-arm64'."
    exit 1
fi

MSAT_DIR="$2"
MSAT_SRC_DIR="$MSAT_DIR/include"
MSAT_LIB_DIR="$MSAT_DIR/lib"
MSAT_BIN_DIR="$MSAT_DIR/bin"

GMP_DIR="$3"
GMP_LIB_DIR="$GMP_DIR/.libs"

SRC_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.c"
OBJ_FILES="org_sosy_1lab_java_1smt_solvers_mathsat5_Mathsat5NativeApi.o"

check_requirements "$MSAT_LIB_DIR/libmathsat.a" "You need to specify the directory with the downloaded MathSAT5 on the command line!"
check_requirements "$GMP_LIB_DIR/libgmp.a" "You need to specify the directory with the downloaded and compiled GMP on the command line!"
if [ "$ARCH" == "linux-arm64" ]; then # on linux-x64, we use the installed default JDK
  check_requirements "$JNI_DIR/jni.h" "You need to specify the directory with the downloaded JNI headers on the command line!"
fi

rm "$OBJ_FILES"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the MathSAT5 header files
$CC -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter \
    $JNI_HEADERS -I$MSAT_SRC_DIR -I$GMP_DIR $SRC_FILES -fPIC -c

echo "Compilation Done"
echo "Linking libraries together into one file..."

# This will link together the file produced above, the MathSAT5 library, the GMP library and the standard libraries.
# Everything except the standard libraries is included statically.
# The result is a single shared library containing all necessary components.
$CC -Wall -g -o ${OUT_FILE} -shared -Wl,-soname,${OUT_FILE} \
    -L. -L${MSAT_LIB_DIR} -L${GMP_LIB_DIR} -I${GMP_DIR} ${OBJ_FILES} \
    -Wl,-Bstatic -lmathsat -lgmpxx -lgmp -static-libstdc++ -lstdc++ \
    -Wl,-Bdynamic -lc -lm

if [ $? -ne 0 ]; then
    echo "There was a problem during compilation of \"$SRC_FILES\""
    exit 1
fi

echo "Linking Done"
echo "Reducing file size by dropping unused symbols..."

$STRIP ${OUT_FILE}

echo "Reduction Done"

MISSING_SYMBOLS="$(readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND)"
echo "Missing symbols: '$MISSING_SYMBOLS'"
if [ ! -z "$MISSING_SYMBOLS" ]; then
    echo "Warning: There are the following unresolved dependencies in libmathsat5j.so:"
    echo "Missing symbols: '$MISSING_SYMBOLS'"
    readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND
    exit 1
fi

echo "All Done"

echo "Please check the following dependencies that will be required at runtime by ${OUT_FILE}:"
LANG=C objdump -p ${OUT_FILE} | grep -A50 "required from"
