#!/bin/bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

docker build -t registry.gitlab.com/sosy-lab/software/java-smt/develop:ubuntu1804 - < ubuntu1804.Dockerfile

# Please use the following commands to push the build image to Gitlab:
#
# docker login registry.gitlab.com
# docker push registry.gitlab.com/sosy-lab/software/java-smt/develop:ubuntu1804
