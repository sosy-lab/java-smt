#!/bin/bash

# specific for my system:
# JavaSMT and all solver files are located in the directory "workspace".
WORKSPACE=$HOME/workspace

docker run -it \
    --mount type=bind,source=${WORKSPACE},target=/workspace \
    -u $(id -u ${USER}):$(id -g ${USER}) \
    devel:ubuntu1804
