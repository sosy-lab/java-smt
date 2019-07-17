#/usr/bin/env/ bash
set -e

# remove STP repo
[ -d "./stp" ] && rm -rf ./stp ||:


# the built STP library should have been copied out 
[ -d "./stpJ/build" ] && rm -rf ./stpJ/build ||:

#remove cryptominisat repo
[ -d "./dependencies/cryptominisat" ] && rm -rf ./dependencies/cryptominisat ||:

# java builds

echo "Build files and cloned repos removed."
