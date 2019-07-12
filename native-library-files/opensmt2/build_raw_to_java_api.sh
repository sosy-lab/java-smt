#!/usr/bin/etc/ bash

set -e

# get or locate the project
# build it as a shared library

# --- POSSIBLE LIBRARY FILES:
# ./build/src/bin/CMakeFiles/exec.dir/opensmt.C.o
# ./build/src/api/libopensmt2.so

# FILE="$(pwd)"/opensmt/build/src/api/libopensmt2.so
FILE=./opensmt/build/src/api/libopensmt2.so

# echo $FILE
echo ---
if [! -e "$FILE" ]; then
	echo "I can't find the opensmt library file. I am making a new one ..."
    sh clean_clone_build.sh
fi

cp $FILE ./opensmt2J/lib/
echo "opensmt library file now copied to ./opensmt2J/lib/ for convinience"

# create or locate the SWIG interface to this project
# cmake build a new API linking :
	#- SWIG interface
	#- project .so
	#- source file referenced in the SWIG interface (if any)

cd ./opensmt2J
[ ! -f ./build ] && mkdir ./build || rm -rf ./build/* ||:

cd ./build

echo "Now building the JAVA API for OpenSMT ..."

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build . 

echo
echo "BUILD SUCCESSFUL"
echo

ls
	
# copy API - jar and - so into javasmt
echo
echo "copying library files into JavaSMT (old files are overwritten) ... ...."

cp ./opensmt2JavaAPI.jar /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/
cp ./libopensmt2api.so /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/native/x86_64-linux/

echo "SUCCESS"

