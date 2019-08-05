#!/usr/etc/ bash

set -e
# prerequisite for building STP
#  boost, flex, bison and minisat
sudo apt-get install cmake bison flex libboost-all-dev python perl minisat

# CryptoMiniSat 
git clone https://github.com/msoos/cryptominisat
cd cryptominisat
mkdir build && cd build
cmake ..
make
sudo make install
sudo ldconfig
