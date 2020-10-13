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

## CVC4

 - Our version of CVC4 does not support any garbage collection in the native library.
   This might cause memory leaks.

[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
