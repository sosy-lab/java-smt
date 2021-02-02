#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# #########################################
#
# INFO:
# This script has to be used with the Yices2 and GMP installed as explained
# below in Windows with Cygwin!
#
# #########################################
# 
# Information as to how to compile Yices2 for Windows: https://github.com/SRI-CSL/yices2/blob/master/doc/COMPILING
# Information as to how to compile GMP for Windows for Yices2: https://github.com/SRI-CSL/yices2/blob/master/doc/GMP
# Note: Cygwin is needed for compiliation, but the binary can be build in a way that it is not needed for execution.
# 
# Install Cygwin https://www.cygwin.com/
# Note: choose to install "mingw64-x86_64-gcc-..." (at least core and g++), 
#   "mingw64-x86_64-headers", "mingw64-x86_64-runtime", "gcc-core", "gcc-g++",
#   "libgcc", "cmake", "bash", "m4" and "make", "automake", "autoconf2.1",
#   "autoconf2.5", "autoconf" (the wrapper thingy), "libtool" and "gperf"
# If you miss to install them, just restart the installation file and you can choose them.
# 
# It might be possible that you need to install MinGW first 
# and the cross-compiler in Cygwin ("mingw64-x86_64-gcc-...") after that.
# 
# Install MinGW http://www.mingw.org
# Note: Do not install MinGW in any location with spaces in the path name!
# The preferred installation target directory is C:\MinGW
# 
# Yices2 needs the static and dynamic version of GMP 
# and Windows doesn't allow both to be installed in the same dir, so we need to install it twice.
# 
# Building GMP(shared) 64:
# 
#     Download GMP https://gmplib.org/
#     Switch to Cygwin
# 
#     Unzip/Untar your GMP download to a location ${gmp_build} with for example:
#     cd ${gmp_build}
#     tar -xf ${gmp_download}/gmp-x.x.x.tar.gz //for a tar.xz ball
# 
#     cd into/new/gmp/dir
#     We need to set mingw64 as compiler. 
#     CC NM and AR need to match your installed mingw (located at /usr/bin ).
#     The --prefix is the install location. You can change it, but remember where you put it.
# 
#     ./configure --disable-static --enable-shared --prefix=/usr/tools/shared-gmp \
#     --host=x86_64-pc-mingw32 --build=i686-pc-cygwin CC=/usr/bin/x86_64-w64-mingw32-gcc \
#     NM=/usr/bin/x86_64-w64-mingw32-nm AR=/usr/bin/x86_64-w64-mingw32-ar CC_FOR_BUILD=gcc
#
#     make
#     make check
#     make install
# 
#     That should have "installed" the following files that we need:
# 
#     /usr/tools/static-gmp/bin/libgmp-10.dll (DLL)
#     /usr/tools/static-gmp/lib/libgmp.dll.a (import library)
#     /usr/tools/static-gmp/lib/libgmp.la (stuff used by libtool)
#     /usr/tools/static-gmp/include/gmp.h
# 
# Building GMP (static) 32:
# 
#     Go back to the dir you Unzipped the tarball (same as shared)
# 
#     The following installs the static GMP to /tools/static_gmp but you can change that of course:
#     You need to use "make clean" after a failed make or it might not configure correctly!
#
#     ./configure --disable-shared --enable-static --prefix=/usr/tools/static-gmp \
#     --host=x86_64-pc-mingw32 --build=i686-pc-cygwin CC=/usr/bin/x86_64-w64-mingw32-gcc \
#     NM=/usr/bin/x86_64-w64-mingw32-nm AR=/usr/bin/x86_64-w64-mingw32-ar CC_FOR_BUILD=gcc
#
#     make
#     make check
#     make install
# 
#     This should have installed:
# 
#     /usr/tools/static-gmp/lib/libgmp.a
#     /usr/tools/static-gmp/include/gmp.h
# 
# 
# Now we build Yices2 (The Yices2 documentation gives 2 options to configure yices2 here. I used the second.)
#     You may need to edit the compiler etc. just like in step 5 + specify where you have installed your GMP
#     (CPPFLAGS, LDFLAGS point to the shared GMP. with-static-gmp, with-static-gmp-include-dir point to the static GMP)
#     After using configure you need to give 'OPTION=mingw64' to every make command. 
#     (including make clean)
# 
#     ./configure --build=x86_64-pc-mingw32 CC=/usr/bin/x86_64-w64-mingw32-gcc \
#     LD=/usr/bin/x86_64-w64-mingw32-ld STRIP=/usr/bin/x86_64-w64-mingw32-strip \
#     RANLIB=/usr/bin/x86_64-w64-mingw32-ranlib CPPFLAGS=-I/usr/tools/shared-gmp/include \
#     LDFLAGS=-L/usr/tools/shared-gmp/lib --with-static-gmp=/usr/tools/static-gmp/lib/libgmp.a \
#     --with-static-gmp-include-dir=/usr/tools/static-gmp/include --host=x86_64-w64-mingw32
# 
#     make OPTION=mingw64
# 
# Build the JNI wrapper dll:
#     To build yices2 bindings: ./compileForWindows.sh $YICES_SRC_DIR $SHARED_GMP_SRC_DIR $JNI_DIR
#     
#     After running the script, copy the libyices.dll from the Yices2 folder 
#     (yices2/build/x86_64-unknown-mingw32-release/bin) and the libyices2j.dll 
#     to java-smt\lib\native\x86_64-windows or publish it.
# 


SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

JNI_DIR="$3"/include
JNI_HEADERS="-I${JNI_DIR}/ -I${JNI_DIR}/win32/"

YICES_SRC_DIR="$1"
YICES_RLS_DIR="$1"/build/x86_64-unknown-mingw32-release

SHARED_GMP_SRC_DIR="$2"

SRC_FILES="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c"

# check requirements
if [ ! -f "$YICES_RLS_DIR/bin/libyices.dll" ]; then
    echo "You need to specify the directory with the built yices2 on the command line!"
    echo "Can not find $YICES_RLS_DIR/bin/libyices.dll"
    exit 1
fi
if [ ! -f "$JNI_DIR/jni.h" ]; then
    echo "You need to specify the directory with the downloaded JNI headers on the command line!"
    echo "Can not find $JNI_DIR/jni.h"
    exit 1
fi

OUT_FILE="libyices2j.dll"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the Mathsat header files
x86_64-w64-mingw32-gcc -g -o $OUT_FILE -shared -Wl,-soname,$OUT_FILE \
    -D_JNI_IMPLEMENTATION_ -Wl,--kill-at $JNI_HEADERS \
    -I$YICES_RLS_DIR/dist/include -L$YICES_RLS_DIR/lib -L$SHARED_GMP_SRC_DIR/include -L. \
    org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c \
    -lyices $YICES_RLS_DIR/bin/libyices.dll -lgmp -L$SHARED_GMP_SRC_DIR/lib \
    -lstdc++

echo "Compilation Done"
echo "Reducing file size by dropping unused symbols..."

strip ${OUT_FILE}

echo "Reduction Done"
echo "All Done"

echo "Please check the following dependencies that will be required at runtime by $OUT_FILE:"
echo "(DLLs like 'kernel32' and 'msvcrt' are provided by Windows)"
objdump -p $OUT_FILE | grep "DLL Name"
