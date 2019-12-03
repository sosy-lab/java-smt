#/usr/bin/env/ bash

# This removes any existing STP repositories and build files
# and clones a new repo and build STP
# 
set -e

DESTN_DIR=$PWD/opensmtJ/install_include

[ ! -f "$DESTN_DIR" ] && mkdir -p "$DESTN_DIR" || rm -rf "$DESTN_DIR"/* ||:

[ -d "./build" ] && rm -rf ./build ||:
[ -d "./opensmtJ/build" ] && rm -rf ./opensmtJ/build ||:

echo "Raw OpenSMT Build files removed "

#echo "Now copying necessary files to expend STP"
# STP_HEADER=$PWD/stp/include/stp/
# yes | cp -f $PWD/stp_extend/c_interface.h $STP_HEADER
# STP_INTERFACE_SRC=$PWD/stp/lib/Interface/
# yes | cp -f $PWD/stp_extend/ext_c_interface.cpp $STP_INTERFACE_SRC
# yes | cp -f $PWD/stp_extend/CMakeLists.txt $STP_INTERFACE_SRC

cd opensmt
[ -d "./build" ] && rm -rf ./build/*;cd ./build || mkdir ./build;cd ./build ||:
echo
echo "Now rebuilding OpenSMT ... "

cmake .. #-DCMAKE_BUILD_TYPE=Debug
cmake --build .

echo "Installing OpenSMT into $DESTN_DIR"
make DESTDIR=$DESTN_DIR install

echo "... ... OpenSMT BUILD SUCCESSFULL"
ls 
echo

# cd ../../
