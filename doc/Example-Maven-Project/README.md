<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# JavaSMT Maven Example

This project shows how to use JavaSMT in a Maven-based environment.
It includes a main application that lists available solvers and a test case that solves a Sudoku puzzle.
The configuration in `pom.xml` handles the download and setup of native solver libraries (e.g., Z3, MathSAT5, CVC5) so they can be loaded by the JVM.

## Prerequisites

* Java 17 or newer.
* Apache Maven.
* Native solvers are only provided for **Linux x64** in this example. 
  Some solvers like Z3 and MathSAT5 also support Windows or ARM64 platform, if dependencies are adjusted in `pom.xml`.
  Java-only solvers (SMTInterpol, Princess) work on all platforms.
* When using Linux, please use Ubuntu 24.04 or newer, as we require GLIBC_2.33 or newer for some of the latest solver versions.

## Usage

### Compile and Build

Run the following to download dependencies and build the project:
```bash
mvn clean compile
```
Native libraries will be copied and renamed in `target/dependency`.

### Run the Solver Overview Table

This application prints a table of detected solvers and their features.

```bash
mvn package
java -jar ./target/java-smt-maven-example-VERSION.jar
```

Or via Maven, using the preconfigured execution configuration from `pom.xml`:
```bash
mvn compile exec:exec
```

Or via Maven, with explicit arguments to set the library path:
```bash
mvn compile exec:exec -Dexec.executable="java" -Dexec.args="-Djava.library.path=target/dependency -cp %classpath org.sosy_lab.java_smt_example.SolverOverviewTable"
```

### Run Sudoku Test

The `SudokuTest` runs against all available solvers.

```bash
mvn test
```

## Project Structure

* `src/main/java/org/sosy_lab/java_smt_example/SolverOverviewTable.java`: Main application.
* `src/test/java/org/sosy_lab/java_smt_example/SudokuTest.java`: Parameterized JUnit test.
* `pom.xml`: Maven configuration including dependency management and native library handling.

## Native Library Handling

JavaSMT backends often require native binaries. This project automates the following steps:
1. Download native libraries via Maven dependencies (using `classifier` and `type`).
2. Copy them to `target/dependency` using `maven-dependency-plugin`.
3. Rename them (e.g., from `javasmt-solver-z3-libz3java-x64.so` to `libz3java.so`) using `maven-antrun-plugin` to match JavaSMT expectations.
4. Set `java.library.path` to this directory during execution.

For more details, see the [JavaSMT documentation](https://github.com/sosy-lab/java-smt).
