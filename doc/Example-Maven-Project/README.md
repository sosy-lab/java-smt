<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

This is an example application for using JavaSMT with Maven.
The example application prints a table of the available SMT solvers,
their version number and supported features.

The Maven workflow in this project supports the following steps:

- Compiling: `mvn compile` downloads all dependencies and compiles the project.
- Testing: `mvn test` executes the Sudoku example test.
- Packaging: `mvn package` creates a jar file for the example application.
  Dependencies like other jar files and binaries for SMT solvers are stored in the directory `dependencies`
- Running: `java -jar ./target/java-smt-maven-example-VERSION.jar` shows a table in the terminal.

Please note that the Maven repository currently only contains release versions
and no snapshots, thus the newest features and bugfixes might be missing.
If a Maven step is not working or more steps are required,
please ask or report an issue [in the project](https://github.com/sosy-lab/java-smt).
