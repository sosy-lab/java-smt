#/usr/bin/env/ bash

# This removes any existing STP repositories and build files
# and clones a new repo and build STP
# 
set -e

DESTN_DIR=$PWD/stpJ/install_include

[ ! -f "$DESTN_DIR" ] && mkdir -p "$DESTN_DIR" || rm -rf "$DESTN_DIR"/* ||:

[ -d "./stp" ] && rm -rf ./stp ||:
[ -d "./build" ] && rm -rf ./build ||:

echo "Build files removed and STP repo deleted."
echo "Now cloning stp ..."

git clone https://github.com/stp/stp.git

echo "Now copying necessary files to expend STP"
STP_HEADER=$PWD/stp/include/stp/
yes | cp -f $PWD/stp_extend/c_interface.h $STP_HEADER
STP_INTERFACE_SRC=$PWD/stp/lib/Interface/
yes | cp -f $PWD/stp_extend/ext_c_interface.cpp $STP_INTERFACE_SRC
yes | cp -f $PWD/stp_extend/CMakeLists.txt $STP_INTERFACE_SRC

cd stp
mkdir ./build;cd ./build
echo
echo "Now building STP ... "

cmake ..
make

echo "Installing STP into $DESTN_DIR"
make DESTDIR=$DESTN_DIR install

echo "... ... STP BUILD SUCCESSFULL"
ls 
echo

# cd ../../
