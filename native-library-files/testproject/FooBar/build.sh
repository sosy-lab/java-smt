#!/usr/bin/etc/ bash

set -e

rm -rf ./build/* ||:
cd ./build

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build .

echo "... ... BUILD SUCCESSFULL"
ls 
echo

cd ..
