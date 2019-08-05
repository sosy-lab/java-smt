#!/usr/bin/etc/ bash

set -e
set -u

# Gets the normal STP library, if not found it is cloned and built.
# Afterwards, using SWIG we define a new API and generate its JNI bindings
# The new API is rebuild as a shared library and the JNI Java classes generated
# The resulting .so library and the binding classes (compile to a .jar) 
# are copied into appropriate folder in java-smt.


STP_LIB=./stp/build/lib/libstp.so


PRJ_DIR="${PWD%/*/*}"
PRJ_NAME=$(basename "$PRJ_DIR")


# confirm expected directory structure 
# MUST BE like java-smt/../../this_script.sh
if [[ "$PRJ_NAME"!="java-smt" ]]
 then
	echo "this script is not place in the proper directory" >&2
	echo "this script expects to reside in somewhere like\
	 .../java-smt/dir_1/dir_2/build_raw_to_java_api.sh" >&2 
	exit 1
fi

# set destination directory for final libraries
JAR_LIB_DIR="${PRJ_DIR}/lib/"
SO_LIB_DIR="${JAR_LIB_DIR}/native/x86_64-linux/


# echo $FILE
echo ---
if [! -f "$STP_LIB" ]; then
	echo "I can't find the STP library file. I am making a new one ..."
    sh clean_clone_build.sh
fi

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
echo "copying library files into JavaSMT (old files are overwritten) ... ..."

# cp ./stpJavaAPI.jar /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/
# cp ./libstpJapi.so /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/native/x86_64-linux/

cp ./stpJavaAPI.jar $JAR_LIB_DIR
cp ./libstpJapi.so $SO_LIB_DIR

echo "SUCCESS"