#!/usr/bin/etc/ bash

set -e

rm -rf ./build/* ||:
echo "./build/  cleaned up"
rm -rf ./normal_build/files/* ||:
echo "./normal_build/files/ cleaned up"
echo
