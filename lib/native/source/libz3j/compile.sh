#!/usr/bin/env bash
# This script searches for all included libraries in the current directory first.
# You can use this to override specific libraries installed on your system.
# You can also use this to force static linking of a specific library,
# if you put only the corresponding .a file in this directory, not the .so file.

# For example, to statically link against libstdc++,
# compile this library with --with-pic,
# and put the resulting libstdc++.a file in this directory.

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

OUTFILENAME="libz3j.so"
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

echo "Building the C wrapper code"
./buildZ3wrapper.py "$Z3_SRC_DIR" > org_sosy_lab_solver_z3_Z3NativeApi.c

echo "Compiling the C wrapper code and creating the \"z3j\" library"

# This will compile the JNI wrapper part, given the JNI and the Z3 header files
$COMPILER_CMD -g $JNI_HEADERS -I$Z3_SRC_DIR org_sosy_lab_solver_z3_Z3NativeApi.c versions.c -fPIC -c

if [ $? -eq 0 ]; then
    echo "JNI wrapper compiled"
else
    echo "There was a problem during compilation of \"org_sosy_lab_solver_z3_Z3NativeApi.o\""
    exit 1
fi

echo "Wrapping the libz3.o with a patched memcpy in order to support legacy systems"
$COMPILER_CMD -Wall -o libz3.so -shared -Wl,-soname,libz3.so versions.o -L. -L$Z3_LIB_DIR -L$Z3_DIR -Wl,-Bstatic,--whole-archive -lz3 -Wl,-Bdynamic,--no-whole-archive,--wrap=memcpy -lrt -lc -lm -lstdc++ -fopenmp

echo "Producing a shared object with JNI bindings"

$COMPILER_CMD -Wall -o $OUTFILENAME -shared -Wl,-soname,$OUTFILENAME -Wl,-rpath,'$ORIGIN' -L. -L$Z3_LIB_DIR -L$Z3_DIR org_sosy_lab_solver_z3_Z3NativeApi.o $Z3_LIBNAME

echo "All linked together"


MISSING_SYMBOLS="$(readelf -Ws $OUTFILENAME | grep NOTYPE | grep GLOBAL | grep UND)"
if [ ! -z "$MISSING_SYMBOLS" ]; then
    echo "Warning: There are the following unresolved dependencies in libz3j.so:"
    readelf -Ws $OUTFILENAME | grep NOTYPE | grep GLOBAL | grep UND
    exit 1
fi

MISSING_SYMBOLS="$(readelf -Ws $Z3_LIB_DIR/$Z3_SO_FILENAME | grep NOTYPE | grep GLOBAL | grep UND)"
if [ ! -z "$MISSING_SYMBOLS" ]; then
    echo "Warning: There are the following unresolved dependencies in libz3.so:"
    readelf -Ws $Z3_LIB_DIR/$Z3_SO_FILENAME | grep NOTYPE | grep GLOBAL | grep UND
    exit 1
fi

echo "All Done"
