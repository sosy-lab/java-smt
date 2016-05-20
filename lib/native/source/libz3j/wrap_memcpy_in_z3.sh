#!/usr/bin/env bash

# Enable error handling.
set -o nounset
set -o pipefail

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
    DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
    SOURCE="$(readlink "$SOURCE")"
    [[ $SOURCE != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd $DIR

JNI_HEADERS="$(../get_jni_headers.sh)"

Z3_SO_FILENAME="libz3.so"
Z3_ARCHIVE_FILENAME="libz3.a"
COMPILER_CMD="gcc"
Z3_LIBNAME="-lz3"

Z3_DIR="$1"
Z3_SRC_DIR="$Z3_DIR"/src/api
Z3_LIB_DIR="$Z3_DIR"/build
if [ ! -f "$Z3_LIB_DIR/$Z3_SO_FILENAME" ]; then
    echo "You need to specify the directory with the successfully built Z3 on the command line!"
    exit 1
fi
if [ ! -f "$Z3_LIB_DIR/$Z3_ARCHIVE_FILENAME" ]; then
    echo "Static build of Z3 is necessary, perhaps run ./configure --staticlib"
    exit 1
fi

# Create memcpy_wrapper.o
$COMPILER_CMD memcpy_wrapper.c -fPIC -c

echo "Wrapping the libz3.a with a patched memcpy in order to support legacy systems"
$COMPILER_CMD -Wall -o libz3.so -shared -Wl,-soname,libz3.so memcpy_wrapper.o -L. -L$Z3_LIB_DIR -L$Z3_DIR -Wl,-Bstatic,--whole-archive -lz3 -Wl,-Bdynamic,--no-whole-archive,--wrap=memcpy -lrt -lc -lm -lstdc++ -fopenmp

MISSING_SYMBOLS="$(readelf -Ws $Z3_SO_FILENAME | grep NOTYPE | grep GLOBAL | grep UND)"
if [ ! -z "$MISSING_SYMBOLS" ]; then
    echo "Warning: There are the following unresolved dependencies in libz3.so:"
    readelf -Ws $Z3_SO_FILENAME | grep NOTYPE | grep GLOBAL | grep UND
    exit 1
fi

echo "All Done"
