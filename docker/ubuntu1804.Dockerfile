# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:18.04

# set default locale
RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC apt-get install -y \
        tzdata locales locales-all \
 && apt-get clean
ENV LC_ALL=en_US.UTF-8
ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US.UTF-8

# Install basic packages for building several solvers
RUN apt-get update \
 && apt-get install -y \
        wget curl git build-essential cmake patchelf unzip \
        openjdk-11-jdk ant maven \
        gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
        binutils-aarch64-linux-gnu libc6-dev-arm64-cross \
        mingw-w64 zlib1g-dev m4 \
 && apt-get clean

# Yices2 requires some dependencies
RUN apt-get update \
 && apt-get install -y \
        autoconf gperf \
 && apt-get clean

# Bitwuzla requires Ninja and Meson (updated version from pip), and uses SWIG >4.0 from dependencies.
# GMP >6.3.0 is automatically downloaded and build within Bitwuzla.
RUN apt-get update \
 && apt-get install -y \
        ninja-build python3-pip \
 && apt-get clean
RUN pip3 install --upgrade meson

# OpenSMT requires swig, gmp, flex and bison
# - swig needs to built manually to get version 4.1 for unique_ptr support
# - libpcre2-dev is a dependency of swig
# - gmp needs to be recompiled to generate PIC code (see below)
# - lzip is required to unpack the gmp tar ball
RUN apt-get update \
 && apt-get install -y \
        cmake flex bison libpcre2-dev lzip \
 && apt-get clean

WORKDIR /dependencies

# Install SWIG in a recent enough version
RUN wget http://prdownloads.sourceforge.net/swig/swig-4.1.1.tar.gz \
 && tar xf swig-4.1.1.tar.gz \
 && rm swig-4.1.1.tar.gz \
 && cd swig-4.1.1 \
 && ./configure \
 && make -j4 \
 && make install \
 && cd .. \
 && rm -rf swig-4.1.1

# Install GMP for linux on x64 and arm64
# We could add another build for windows when needed
RUN wget https://gmplib.org/download/gmp/gmp-6.2.1.tar.lz \
 && tar xf gmp-6.2.1.tar.lz \
 && rm gmp-6.2.1.tar.lz \
 && cd gmp-6.2.1 \
 && ./configure \
      --enable-cxx \
      --with-pic \
      --disable-shared \
      --enable-fat \
      --prefix=/dependencies/gmp-6.2.1/install/x64-linux \
 && make -j4 \
 && make install \
 && make clean \
 && ./configure \
      --enable-cxx \
      --with-pic \
      --disable-shared \
      --enable-fat \
      --host=aarch64-linux-gnu \
      --prefix=/dependencies/gmp-6.2.1/install/arm64-linux \
 && CC=aarch64-linux-gnu-gcc CXX=aarch64-linux-gnu-g++ LD=aarch64-linux-gnu-ld make -j4 \
 && make install \
 && make clean

# Install the Jdk for Windows x64
RUN wget https://download.java.net/openjdk/jdk11/ri/openjdk-11+28_windows-x64_bin.zip \
 && unzip openjdk-11+28_windows-x64_bin.zip \
 && mv jdk-11 jdk11-windows-x64 \
 && rm openjdk-11+28_windows-x64_bin.zip

# Install the Jdk for Linux arm64
RUN wget https://download.java.net/java/GA/jdk17.0.2/dfd4a8d0985749f896bed50d7138ee7f/8/GPL/openjdk-17.0.2_linux-aarch64_bin.tar.gz \
 && tar -xzf openjdk-17.0.2_linux-aarch64_bin.tar.gz \
 && mv jdk-17.0.2 jdk17-linux-aarch64 \
 && rm openjdk-17.0.2_linux-aarch64_bin.tar.gz

# JNI is not found when compiling Boolector in the image, so we need to set JAVA_HOME
ENV JAVA_HOME=/usr/lib/jvm/java-11-openjdk-amd64/

# set labels for the image
ARG BUILD_DATE
LABEL org.opencontainers.image.created="${BUILD_DATE}"
LABEL org.opencontainers.image.title="JavaSMT solver development"
LABEL org.opencontainers.image.description="Ubuntu 18.04-based image for JavaSMT solver development"
LABEL org.opencontainers.image.source="https://github.com/sosy-lab/java-smt"
LABEL org.opencontainers.image.licenses="Apache-2.0"

# Podman-Specific Label for Auto-Update
LABEL io.containers.autoupdate=registry
