<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# Known Solver Issues

## Princess

 - Princess is recursive and might require a large amount of stack memory.
If you experience stack overflows or Princess returns `OutOfMemory`,
try increasing the stack size with the JVM parameter `-Xss`.
 - Requesting termination via the [ShutdownNotifier][] works only in limited circumstances.

## SMTInterpol

 - SMTInterpol does not support multiple concurrent stacks under the same context.
 - With JavaSMT up to 1.0.1,
variables and UFs that are used for the first time after a solver stack has been created
will be deleted on the next call to `pop()` and will be invalid afterwards.
This will be changed in the next release of JavaSMT such that variable declarations
in SMTInterpol work like those in other solvers.

## Z3

 - Z3 interpolation procedure might require a large amount of stack memory.
If you get segmentation fault on interpolation, try increasing the stack size 
with the JVM parameter `-Xss`.

[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
