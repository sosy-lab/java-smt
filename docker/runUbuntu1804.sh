#!/bin/bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# JavaSMT and all solver files are located in the directory WORKSPACE.
# Derive WORKSPACE from the script's location (two directories up from current)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE="$(realpath "${SCRIPT_DIR}/../..")"

podman run -it \
    --mount type=bind,source=${WORKSPACE},target=/workspace \
    --workdir /workspace/java-smt \
    registry.gitlab.com/sosy-lab/software/java-smt/develop:ubuntu1804
