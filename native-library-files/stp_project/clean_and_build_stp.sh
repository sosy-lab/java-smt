#/usr/bin/env/ bash

# This removes raw STP buld files and rebuild it
# 
set -e

DESTN_DIR=$PWD/stpJ/install_include

[ ! -f "$DESTN_DIR" ] && mkdir -p "$DESTN_DIR" || rm -rf "$DESTN_DIR"/* ||:

[ -d "./stp/build" ] && rm -rf ./stp/build ||:
[ -d "./build" ] && rm -rf ./build ||:

echo "Raw STP Build files removed "

echo "Now copying necessary files to expend STP"
STP_HEADER=$PWD/stp/include/stp/
yes | cp -f $PWD/stp_extend/c_interface.h $STP_HEADER
STP_INTERFACE_SRC=$PWD/stp/lib/Interface/
yes | cp -f $PWD/stp_extend/ext_c_interface.cpp $STP_INTERFACE_SRC
yes | cp -f $PWD/stp_extend/CMakeLists.txt $STP_INTERFACE_SRC

cd stp
mkdir ./build;cd ./build
echo
echo "Now rebuilding building STP ... "


cmake ..
make

echo "Installing STP into $DESTN_DIR"
make DESTDIR=$DESTN_DIR install

echo "... ... STP BUILD SUCCESSFULL"
ls 
echo

# cd ../../
