#!/bin/bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

#------------------------------------------------------------------------------
# check Java version
#------------------------------------------------------------------------------

set -e

[ -z "$JAVA" ] && JAVA=java
java_version="`$JAVA -XX:-UsePerfData -Xmx5m -version 2>&1`"
result=$?
if [ $result -eq 127 ]; then
  echo "Java not found, please install Java 11 or newer." 1>&2
  echo "For Ubuntu: sudo apt-get install openjdk-11-jre" 1>&2
  echo "If you have installed Java 11, but it is not in your PATH," 1>&2
  echo "let the environment variable JAVA point to the \"java\" binary." 1>&2
  exit 1
fi
if [ $result -ne 0 ]; then
  echo "Failed to execute Java VM, return code was $result and output was"
  echo "$java_version"
  echo "Please make sure you are able to execute Java processes by running \"$JAVA\"."
  exit 1
fi
java_version="`echo "$java_version" | grep -e "^\(java\|openjdk\) version" | cut -f2 -d\\\" | cut -f1 -d.`"
if [ -z "$java_version" ] || [ "$java_version" -lt 11 ] ; then
  echo "Your Java version is too old, please install Java 11 or newer." 1>&2
  echo "For Ubuntu: sudo apt-get install openjdk-11-jre" 1>&2
  echo "If you have installed Java 11, but it is not in your PATH," 1>&2
  echo "let the environment variable JAVA point to the \"java\" binary." 1>&2
  exit 1
fi

#------------------------------------------------------------------------------
# build classpath for JavaSMT
#------------------------------------------------------------------------------

platform="`uname -s`"
SEP=":"

# where the project directory is, relative to the location of this script
case "$platform" in
  Linux|CYGWIN*)
    SCRIPT="$(readlink -f "$0")"
    [ -n "$PATH_TO_JAVASMT" ] || PATH_TO_JAVASMT="$(readlink -f "$(dirname "$SCRIPT")")"
    ;;
  MINGW64*)
	PATH_TO_JAVASMT="." # assume working directory is the current directory
	SEP=";"
    ;;
  # other platforms like Mac don't support readlink -f
  *)
    [ -n "$PATH_TO_JAVASMT" ] || PATH_TO_JAVASMT="$(dirname "$0")"
    ;;
esac

if [ ! -e "$PATH_TO_JAVASMT/bin/org/sosy_lab/java_smt/example/AllSatExample.class" ] ; then
  if [ ! -e "$PATH_TO_JAVASMT/javasmt.jar" ] ; then
    echo "Could not find JAVASMT binary, please check path to project directory" 1>&2
    exit 1
  fi
fi

case "$platform" in
  CYGWIN*)
    JAVA_VM_ARGUMENTS="$JAVA_VM_ARGUMENTS -classpath `cygpath -wp $CLASSPATH`"
    ;;
esac

# build the classpath including all solvers
CLASSPATH="$CLASSPATH$SEP$PATH_TO_JAVASMT/bin$SEP$PATH_TO_JAVASMT/lib/java/core/*"
SOLVERS="bitwuzla boolector cvc4 cvc5 mathsat opensmt optimathsat princess smtinterpol yices2 z3
z3-legacy"
for solver in $SOLVERS ; do
  CLASSPATH="$CLASSPATH$SEP$PATH_TO_JAVASMT/lib/java/runtime-$solver/*"
done

# Run Examples for Java-SMT.
# PerfDisableSharedMem avoids hsperfdata in /tmp (disable it to connect easily with VisualConsole and Co.).

for EXAMPLE in AllSatExample HoudiniApp Interpolation OptimizationFormulaWeights OptimizationIntReal SolverOverviewTable; do
  tput setaf 2 # set green color
  echo ""
  echo "####################################################"
  echo "#  executing example '$EXAMPLE'"
  echo "####################################################"
  echo ""
  tput sgr 0 # reset color
  "$JAVA" \
      -XX:+PerfDisableSharedMem \
      -Djava.awt.headless=true \
      -ea \
      -cp "$CLASSPATH" \
      $JAVA_VM_ARGUMENTS \
      org.sosy_lab.java_smt.example.$EXAMPLE
done
