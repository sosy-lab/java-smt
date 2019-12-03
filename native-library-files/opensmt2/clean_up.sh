#/usr/bin/env/ bash
set -e

#[ -d "./opensmt" ] && rm -rf ./opensmt ||:
[ -d "./build" ] && rm -rf ./build ||:
mkdir ./build

echo "Build files removed."
