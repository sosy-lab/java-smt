#!/bin/bash

set -e

rm -rf boolector

git clone https://github.com/boolector/boolector
cp interface_wrap.c CMakeLists.txt boolector/src/

cd boolector

# include background sat solvers
./contrib/setup-picosat.sh
./contrib/setup-minisat.sh
./contrib/setup-lingeling.sh
./contrib/setup-cadical.sh

# include parser
./contrib/setup-btor2tools.sh

# build Boolector
./configure.sh -fno-strict-aliasing -fpic --shared && cd build && make

cd ../..

# cleanup and copy files where needed
strip boolector/deps/install/lib/libpicosat.so
cp boolector/deps/install/lib/libpicosat.so ../x86_64-linux/

strip boolector/deps/install/lib/libminisat.so
cp boolector/deps/install/lib/libminisat.so ../x86_64-linux/

strip boolector/build/lib/libboolector.so
patchelf --set-rpath '$ORIGIN' --replace-needed libminisat.so.2 libminisat.so boolector/build/lib/libboolector.so
cp boolector/build/lib/libboolector.so ../x86_64-linux/
