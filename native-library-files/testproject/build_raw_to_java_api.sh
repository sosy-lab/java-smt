#!/usr/bin/etc/ bash

set -e

# get or locate the project
# build it as a shared library

cd ./FooBar
sh build.sh
# library is here => ./FooBar/build/libfoobar.so

# copy the .so file to a convinient location
echo
echo "copying raw native library for convinience ... ...."
cp ./build/libfoobar.so ../java_api_build/lib/

# create or locate the SWIG interface to this project
# cmake build a new API linking :
	#- SWIG interface
	#- project .so
	#- source file referenced in the SWIG interface (if any)

cd ../java_api_build
sh build_JAVA_api.sh
	
# copy API - jar and - so into javasmt
echo
echo "copying library files into JavaSMT ... ...."
cp ./build/FoobarJavaAPI.jar /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/
cp ./build/libfoobarapi.so /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/native/x86_64-linux/
echo "SUCCESS"

