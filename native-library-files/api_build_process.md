## CREATING JAVA API TO OPENSMT ##

**1.** clone the repo in a seprate folder

**2.** build normally following the official guidelines

***SCRIPT FOR STEP 1 and 2***

```
#/usr/bin/env/ bash
set -e

[ -d "./opensmt" ] && rm -rf ./opensmt ||:
[ -d "./build" ] && rm -rf ./build ||:
#mkdir ./build

echo "Build files removed and Opemsmt repo deleted."
echo "Now cloning opensmt ..."

git clone https://github.com/usi-verification-and-security/opensmt.git

cd opensmt
#rm -rf ./build/* ||:

mkdir ./build;cd ./build
echo
echo "Now building OpenSMT ... "

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build .

echo "... ... OpenSMT BUILD SUCCESSFULL"
ls 
echo

cd ../../
```

**3.** for coninience create a seprate folder for the Java API library

**4.** Locate and Copy out the shared library created in step 2. as part of the build into the new folder

**5.** Create the SWIG interface to the OpenSMT library (I have used the C language interface provide as it is, for now)

**6.** Create CmakeLists.txt to build the SWIG interface into a JAVA API for OpenSMT

**7.** Run the build - many files are generated but we are only interested in a newly created OpenSMT library (libopensmtapi.so) which we can now interface with through another generated file - a Jar file containing compiled classes. Theses classes can be customised more in terms of naming, documentation, etc using the SWIG Interface created in step 5.

**8.** Copy the .so file and .jar file into appropriate folders inside JavaSMT

***SCRIPT FOR STEP 3 and 8***


```
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


```