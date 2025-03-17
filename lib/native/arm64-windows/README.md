<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# How to install a SMT solver library for Windows (arm64) for developers of JavaSMT

Currently, the only native solver that is supported on Windows for arm64 is Z3. The Java based
solvers SMTInterpol and Princess are also available and will simply work out of the box. To use
Z3 on arm64 its native libraries first need to be linked or copied to this directory. This can
be done just as described in the `README` for Windows on x86 [here](../x86_64-windows/README.md)

Either link the library as admin:
- mklink libz3.dll ..\\..\\java\\runtime-z3\\arm64\\libz3.dll
- mklink libz3java.dll ..\\..\\java\\runtime-z3\\arm64\\libz3java.dll

...or copy the library files directly to this folder:
- copy ..\\..\\java\\runtime-z3\\arm64\\libz3.dll libz3.dll
- copy ..\\..\\java\\runtime-z3\\arm64\\libz3java.dll libz3java.dll
