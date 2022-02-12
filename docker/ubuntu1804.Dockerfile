# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:bionic

RUN apt-get update \
 && apt-get install -y \
        wget curl git \
        build-essential cmake patchelf \
        openjdk-11-jdk ant maven \
        mingw-w64 zlib1g-dev m4

# Add the user "developer" with UID:1000, GID:1000, home at /developer.
# This allows to map the docker-internal user to the local user 1000:1000 outside of the container.
# This avoids to have new files created with root-rights.
RUN groupadd -r developer -g 1000 \
 && useradd -u 1000 -r -g developer -m -d /developer -s /sbin/nologin -c "JavaSMT Development User" developer \
 && chmod 755 /developer

USER developer

# JNI is not found when compiling Boolector in the image, so we need to set JAVA_HOME
ENV JAVA_HOME=/usr/lib/jvm/java-11-openjdk-amd64/
