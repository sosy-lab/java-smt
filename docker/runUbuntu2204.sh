#!/bin/bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# specific for my system:
# JavaSMT and all solver files are located in the directory "workspace".
WORKSPACE=$HOME/workspace

podman run -it \
    --mount type=bind,source=${WORKSPACE},target=/workspace \
    --workdir /workspace/java-smt \
    registry.gitlab.com/sosy-lab/software/java-smt/develop:ubuntu2204
