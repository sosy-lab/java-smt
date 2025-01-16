#!/bin/sh

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

if [ "$(uname)" = "Darwin" ] ; then
  java_home=`readlink -f \`which java\``
  java_home=`echo $java_home | sed 's#/jre/bin/java##' | sed 's#/bin/java##'`
  echo "-I/usr/local/include -I/sw/include -I/System/Library/Frameworks/JavaVM.framework/Headers -I${java_home}/include/ -I${java_home}/include/darwin/"
  LINK_OPT="-dynamiclib -o libJOct.jnilib"
elif [ `uname` = "Linux" ] ; then
  java_home=`readlink -f \`which java\``
  java_home=`echo $java_home | sed 's#/jre/bin/java##' | sed 's#/bin/java##'`
  echo "-I$java_home/include/ -I$java_home/include/linux/"
elif [[ `uname` == CYGWIN* ]] ; then
  java_home_dos=`cygpath -d "$JAVA_HOME"`
  java_home=`cygpath -u "$java_home_dos"`
  echo "-I$java_home/include/ -I$java_home/include/linux/"
else
  echo "Missing build information for `uname`" >&2
  exit 1
fi
