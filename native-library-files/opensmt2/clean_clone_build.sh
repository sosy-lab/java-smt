#/usr/bin/env/ bash
set -e

[ -d "./opensmt" ] && rm -rf ./opensmt ||:
[ -d "./build" ] && rm -rf ./build ||:
#mkdir ./build

echo "Build files removed and Opemsmt repo deleted."
echo "Now cloning opensmt ..."

git clone https://github.com/usi-verification-and-security/opensmt.git

cd opensmt
#rm -rf ./build/* ||:

mkdir ./build;cd ./build
echo
echo "Now building OpenSMT ... "

cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build .

echo "... ... OpenSMT BUILD SUCCESSFULL"
ls 
echo

cd ../../
