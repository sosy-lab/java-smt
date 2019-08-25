#!/usr/bin/etc/ bash

set -e
set -u

# get or locate the project
# build it as a shared library

# --- POSSIBLE LIBRARY FILES:
# ./build/src/bin/CMakeFiles/exec.dir/opensmt.C.o
# ./build/src/api/libopensmt2.so

# OPENSMT2_LIB="$(pwd)"/opensmt/build/src/api/libopensmt2.so
# OPENSMT2_LIB=./opensmt/build/src/api/libopensmt2.so

OPENSMT2_LIB=./opensmt/build/src/api/libopensmt2.so

PRJ_DIR="${PWD%/*/*}"
PRJ_NAME=$(basename "$PRJ_DIR")


# confirm expected directory structure 
# MUST BE like java-smt/../../this_script.sh
if [[ "$PRJ_NAME" != "java-smt" ]]
 then
	echo "this script is not place in the proper directory" >&2
	echo "this script expects to reside in somewhere like\
	 .../java-smt/dir_1/dir_2/build_raw_to_java_api.sh" >&2 
	exit 1
fi

# set destination directory for final libraries
JAR_LIB_DIR="${PRJ_DIR}/lib/"
SO_LIB_DIR="${JAR_LIB_DIR}/native/x86_64-linux/"


# echo $OPENSMT2_LIB

echo ---
if [! -f "$OPENSMT2_LIB" ]
 then
	echo "I can't find the opensmt library file. I am making a new one ..."
    sh clean_clone_build.sh
else 
 echo -n "To rebuild stp press 'y' "
 read re_bld
 if [ "$re_bld" != "${re_bld#[Yy]}" ] ;then
	sh clean_and_build.sh
 fi

fi

# cp $OPENSMT2_LIB ./opensmtJ/lib/
# echo "opensmt library file now copied to ./opensmtJ/lib/ for convinience"

# create or locate the SWIG interface to this project
# cmake build a new API linking :
	#- SWIG interface
	#- project .so
	#- source file referenced in the SWIG interface (if any)

cd ./opensmtJ
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

# cp ./opensmt2JavaAPI.jar /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/
# cp ./libopensmt2api.so /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/native/x86_64-linux/

cp ./opensmt2JavaAPI.jar $JAR_LIB_DIR
cp ./libopensmt2Japi.so $SO_LIB_DIR

echo "SUCCESS"
