#!/usr/bin/etc/ bash

set -e

rm -rf ./FooBar/build/* ||:
echo "./FooBar/build/  cleaned up"
rm -rf ./java_api_build/build/* ||:
echo "./java_api_build/build/ cleaned up"
rm -rf ./java_api_build/lib/* ||:
echo "./java_api_build/lib/ cleaned up"
echo
