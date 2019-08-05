#/usr/bin/env/ bash

# This removes any existing STP repositories and build files
# and clones a new repo and build STP
# 
set -e

[ -d "./stp" ] && rm -rf ./stp ||:
[ -d "./build" ] && rm -rf ./build ||:

echo "Build files removed and STP repo deleted."
echo "Now cloning stp ..."

git clone https://github.com/stp/stp.git

cd stp

mkdir ./build;cd ./build
echo
echo "Now building STP ... "

cmake ..
make
# sudo make install
# sudo ldconfig

echo "... ... STP BUILD SUCCESSFULL"
ls 
echo

# cd ../../
