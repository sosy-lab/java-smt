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

# This script builds the bitwuzla JNI shared library

# For building libbitwuzlaJNI.so, there are several dependencies located all in the bitwuzla folder:
# - Bitwuzla can be found here: https://github.com/bitwuzla/bitwuzla/tree/main
# (Bitwuzla itself needs the GMP library >= 6.1)

# To build Bitwuzla bindings, first you need to compile bitwuzla as shared libary
# then use this script: ./compile.sh $BITWUZLA_DIR


SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

JNI_HEADERS="$(../get_jni_headers.sh)"

BWZL_SRC_DIR="$1"/src
BWZL_LIB_DIR="$1"/lib
BWZL_BUILD_SRC_DIR="$1"/build/src
BWZL_BUILD_LIB_DIR="$1"/build/src/lib
BWZL_INCLUDE_DIR="$1"/include
BWZL_INCLUDE_C_DIR="$1"/include/bitwuzla/c

SRC_FILE="bitwuzla_wrap.c"
OUT_FILE="libbitwuzlaJNI.so"

echo "$1"
echo "$BWZL_SRC_DIR"

# check requirements
if [ ! -f "$BWZL_BUILD_SRC_DIR/libbitwuzla.so.0" ]; then
    echo "compile.sh: the specified directory with the compiled Bitwuzla shared libaries is incorrect. You might need to specify the complete path on the cmd line. Searched directoy: $BWZL_BUILD_SRC_DIR"
    exit 1
fi

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the Bitwuzla header/dependency files
gcc $JNI_HEADERS -I$BWZL_SRC_DIR -I$BWZL_LIB_DIR -I$BWZL_BUILD_SRC_DIR -I$BWZL_BUILD_LIB_DIR -I$BWZL_INCLUDE_DIR -I$BWZL_INCLUDE_C_DIR $SRC_FILE -fPIC -Wall -pedantic -c

# Link
gcc -shared bitwuzla_wrap.o -L$BWZL_BUILD_SRC_DIR -lbitwuzla -Wl,-rpath,$BWZL_BUILD_SRC_DIR -o libbitwuzlaJNI.so

# TODO: improve compiliation process (strict mode), strip lib, check if we can compile static libs and include them

echo "Compilation Done"
echo "All Done"
echo "Please check the following dependencies that will be required at runtime by libbitwuzlaJNI.so:"
LANG=C objdump -p ${OUT_FILE} | grep -A50 "required from"
