#!/usr/bin/env bash

# This script builds libyices2j.so.

# For building libyices2j.so, you need:
# - The Yices2 source as can be downloaded from https://yices.csl.sri.com
#   git clone git@github.com:SRI-CSL/yices2.git
# - Download gperf from https://www.gnu.org/software/gperf/
#   for example: http://ftp.gnu.org/pub/gnu/gperf/gperf-3.1.tar.gz
# - Download GMP from https://gmplib.org
#   for example: https://gmplib.org/download/gmp/gmp-6.1.2.tar.lz
# - Run for GMP and gperf
#   ./configure --enable-cxx --with-pic --disable-shared --enable-fat
#   make -j4
# - Compile Yices2 with
#   autoconf
#   ./configure --with-pic-gmp=../gmp-6.1.2/.libs/libgmp.a
#   make -j4

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

if [ ! -f "$1/build/x86_64-pc-linux-gnu-release/lib/libyices.a" ]; then
	echo "You need to specify the directory with the downloaded and compiled Yices on the command line!"
	exit 1
fi

YICES_SRC_DIR="$1"/src/include
YICES_LIB_DIR="$1"/build/x86_64-pc-linux-gnu-release/lib/
GMP_LIB_DIR="$2"/.libs
GMP_HEADER_DIR="$2"
GPERF_LIB_DIR="$3"/lib
GPERF_HEADER_DIR="$3"

if [ ! -f "$GMP_LIB_DIR/libgmp.a" ]; then
	echo "You need to specify the GMP directory on the command line!"
	exit 1
fi
if [ ! -f "$GPERF_LIB_DIR/libgp.a" ]; then
	echo "You need to specify the GPERF directory on the command line!"
	exit 1
fi

SRC_FILES="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c"
OBJ_FILES="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.o"

OUT_FILE="libyices2j.so"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library"

# This will compile the JNI wrapper part, given the JNI and the Yices header files
gcc -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter \
    $JNI_HEADERS -I$YICES_SRC_DIR -I$GMP_HEADER_DIR -I$GPERF_HEADER_DIR $SRC_FILES -fPIC -c
echo "Compilation Done"

# This will link together the file produced above, the Yices library, the GMP library and the standard libraries.
# Everything except the standard libraries is included statically.
# The result is a shared library.
if [ `uname -m` = "x86_64" ]; then
	gcc -Wall -g -o $OUT_FILE -shared -Wl,-soname,libyices2j.so \
    -L. -L$YICES_LIB_DIR -L$GMP_LIB_DIR -L$GPERF_LIB_DIR \
    -I$GMP_HEADER_DIR -I$GPERF_HEADER_DIR $OBJ_FILES -Wl,-Bstatic \
    -lyices -lgmpxx -lgmp -lgp -static-libstdc++ -lstdc++ \
    -Wl,-Bdynamic -lc -lm -Wl,--version-script=libyices2j.version
else
	gcc -Wall -g -o ${OUT_FILE} -shared -Wl,-soname,libyices2j.so \
    -L${YICES_LIB_DIR} -L${GMP_LIB_DIR} -L${GPERF_LIB_DIR} \
    -I${GMP_HEADER_DIR} -I${GPERF_HEADER_DIR} ${OBJ_FILES} \
    -Wl,-Bstatic -lyices -lgmpxx -lgmp -Wl,-Bdynamic -lc -lm -lstdc++
fi


if [ $? -eq 0 ]; then
	strip ${OUT_FILE}
else
	echo "There was a problem during compilation of
	\"org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c\""
	exit 1
fi

MISSING_SYMBOLS="$(readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND)"
if [ ! -z "$MISSING_SYMBOLS" ]; then
	echo "Warning: There are the following unresolved dependencies in libyices2j.so:"
	readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND
	exit 1
fi

echo "All Done"
