#!/usr/bin/env bash
set -e
set -u

echo
echo "NOW RUNNING THE JAVA SWIG BUILD"
echo

rm -rf ./build/* ||:
cd ./build

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build . #uses the generator to build - "Make" in my case

echo
echo "BUILD SUCCESSFUL"
echo

# JAVA
java -cp . -Djava.library.path=. -jar Main.jar
