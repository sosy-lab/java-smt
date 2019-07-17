#!/usr/bin/etc/ bash

set -e

# get or locate the project
# build it as a shared library

# --- POSSIBLE LIBRARY FILES:
# ./build/src/bin/CMakeFiles/exec.dir/opensmt.C.o
# ./build/src/api/libopensmt2.so

# FILE="$(pwd)"/opensmt/build/src/api/libopensmt2.so

FILE=./stp/build/lib/libstp.so

# echo $FILE
echo ---
if [! -f "$FILE" ]; then
	echo "I can't find the STP library file. I am making a new one ..."
    sh clean_clone_build.sh
fi

# --- copying is no more needed CMAKE should find the library

# [ ! -f ./stpJ/lib/ ] && mkdir ./stpJ/lib/
# cp $FILE ./stpJ/lib/
# echo "STP shared library file now copied to ./stpJ/lib/ for convinience"

# create or locate the SWIG interface to this project
# cmake build a new API linking :
	#- SWIG interface
	#- project .so
	#- source file referenced in the SWIG interface (if any)

cd ./stpJ
[ ! -f ./build ] && mkdir ./build || rm -rf ./build/* ||:

cd ./build

echo "Now building the JAVA API for STP ..."

cmake .. #-DCMAKE_BUILD_TYPE=Debug
cmake --build . 

echo
echo "BUILD SUCCESSFUL"
echo

ls
	
# copy API - jar and - so into javasmt
echo
echo "copying library files into JavaSMT (old files are overwritten) ... ...."

cp ./stpJavaAPI.jar /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/
cp ./libstpJapi.so /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/native/x86_64-linux/

echo "SUCCESS"

