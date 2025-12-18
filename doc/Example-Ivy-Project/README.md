<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

This is an example application for using JavaSMT with Ant/Ivy.
The example application prints a table of the available SMT solvers, along with their version
number.

The project supports the following build steps:

- `resolve` retrieve dependencies with Ivy
- `compile` compile the project
- `package` build a .jar
- `run` run the program
- `clean` clean the project

Calling `ant` with no target will build and then execute the project.