#/usr/bin/env/ bash
set -e

[ -d "./stp" ] && rm -rf ./stp ||:
# [ -d "./build" ] && rm -rf ./build ||:

echo "Build files removed and STP repo deleted."
echo "Now cloning stp ..."

git clone https://github.com/stp/stp.git

cd stp

mkdir ./build;cd ./build
echo
echo "Now building STP ... "

# cmake .. -DCMAKE_BUILD_TYPE=Debug
# cmake -DSHAREDCOMPILE=ON ..
# cmake -DSTATICCOMPILE=ON ..

cmake ..
make
sudo make install
#sudo ldconfig

echo "... ... STP BUILD SUCCESSFULL"
ls 
echo
echo "https://github.com/stp/stp/tree/master/examples/simple"

# cd ../../
