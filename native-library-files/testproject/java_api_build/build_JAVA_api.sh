#!/usr/bin/env bash
set -e
set -u

echo
echo "NOW RUNNING THE JAVA SWIG BUILD"
echo

rm -rf ./build/* ||:
cd ./build

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build . 

echo
echo "BUILD SUCCESSFUL"
echo

