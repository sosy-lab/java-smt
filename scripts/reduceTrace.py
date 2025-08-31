#!/usr/bin/env python3

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import re
import sys
from collections import defaultdict
from pathlib import Path


# Read a trace file
def readTrace(path):
    with open(path) as file:
        return [line.rstrip() for line in file]


# Build a map with line numbers for all variable definitions
def getLinesForDefinitions(trace):
    lineNumber = 1
    lineDefs = dict()
    for line in trace:
        if line.find('=') >= 0:
            leftSide = line[0:(line.find('=') - 1)]
            name = re.match('var (.*)', leftSide)
            lineDefs[name.group(1)] = lineNumber
        lineNumber = lineNumber + 1
    return lineDefs


# Build a dependency graph for the definitions
# Maps from variables to the places where they are used
def buildDependencies(lineDefs, trace):
    lineNumber = 1
    deps = defaultdict(list)
    for line in trace:
        expr = line[(line.find('=') + 2):] if line.find('=') >= 0 else line
        object = expr[0:expr.find('.')]
        if object[0].islower():
            deps[lineDefs[object]].append(lineNumber)
        # FIXME Parse the expression to get the variables
        for m in re.finditer('(config|logger|notifier|var[0-9]+)', expr):
            deps[lineDefs[m.group()]].append(lineNumber)
        lineNumber += 1
    return deps


# Collect all top-level statements
# Top-level statements are:
#  *.addConstraint(*)
#  *.isUnsat()
#  *.getModel()
#  *.asList()
# FIXME Finish this list
def usedTopLevel(lineDefs, trace):
    tl = set()
    for line in trace:
        m = re.fullmatch(
            'var (var[0-9]+) = (var[0-9]+).(isUnsat\\(\\)|getModel\\(\\)|asList\\(\\)|addConstraint\\((var[0-9]+)\\));',
            line)
        if m != None:
            tl.add(lineDefs[m.group(1)])
    return tl


# Calculate the closure of all used definitions, starting with the top-level statements
def usedClosure(tl, deps):
    cl = set()
    st = set(tl)
    while cl.union(st) != cl:
        cl = cl.union(st)
        st = set()
        for (key, val) in deps.items():
            if set(val).intersection(cl) != set():
                st.add(key)
    return cl


# Keep only statements and definitions that are used
def filterUnused(used, trace):
    lineNumber = 1
    reduced = []
    for line in trace:
        if line.find('=') == -1 or lineNumber in used:
            reduced.append(line)
        lineNumber += 1
    return reduced


# Remove all definitions that are not used (recursively)
def removeDeadCode(trace):
    lineDefs = getLinesForDefinitions(trace)
    deps = buildDependencies(lineDefs, trace)
    tl = usedTopLevel(lineDefs, trace)
    cl = usedClosure(tl, deps)
    return filterUnused(cl, trace)


if __name__ == '__main__':
    arg = sys.argv
    if not len(sys.argv) == 2:
        print('Expecting a path to a trace file as argument')
        exit(-1)

    path = Path(sys.argv[1])
    if not (path.is_file()):
        print(f'Could not find file "{path}"')
        exit(-1)

    # We'll use multiple passes to reduce the size of the trace:
    # 1. Read the trace
    # 2. Remove unused code
    # 3. Remove unnecessary toplevel commands
    # 4. Loop: Remove aliasing (by duplicating the definitions)
    # 5.    Loop: Reduce terms
    # 6. Remove unused prover environments

    # TODO Implement steps 3-6
    # TODO Check that the reduced trace still crashes

    trace = readTrace(path)
    for line in removeDeadCode(trace):
        print(line)
