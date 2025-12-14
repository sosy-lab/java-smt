#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

set -e

if [[ $# -eq 0 ]]; then
    echo "No command line for the solver"
    echo "Usage: ./tracingTest.sh <cmd>"
    echo "Where <cmd> is the full command for the solver, including any options that need to be passed"
    exit 1
fi

cmd=$*

echo "Initializing venv"
python3 -m venv .venv
source .venv/bin/activate

pip install -r requirements.txt

echo -e "\nConverting JavaTraces to Smtlib"
find ../traces -name *.java -exec ./traceToSmtlib.py --save {} ';'

echo -e "\nRunning the solver on the generated Smtlib files"
find ../traces -name *.smt2 -exec echo "path: {}" ';' -exec timeout 20s $* {} ';' 2>&1 | tee solver.log | grep -E "error|path"

echo -e "\n(See solver.log for the entire solver output)"

deactivate
