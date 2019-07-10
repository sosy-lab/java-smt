#/usr/bin/env/ bash
set -e

[ -d "./opensmt" ] && rm -rf ./opensmt ||:
[ -d "./build" ] && rm -rf ./build ||:
mkdir ./build

echo "Build files removed and Opemsmt repo deleted."
echo "Now cloning opensmt ..."

git clone https://github.com/usi-verification-and-security/opensmt.git