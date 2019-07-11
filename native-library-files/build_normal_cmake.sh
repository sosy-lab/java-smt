#!/usr/bin/env bash
set -e
set -u

echo
echo "NOW RUNNING A NORMAL BUILD"
echo

cd ./build/

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build . #uses the generator to build - "Make" in my case

echo
echo "BUILD SUCCESSFUL"
echo
echo

ls

# copy the jar file to 
# home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/

# copy the .so file to 
# /home/lubuntu/SAHEED/gsoc/CODE/java-smt/lib/native/x86_64-linux/