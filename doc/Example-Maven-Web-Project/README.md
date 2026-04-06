<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# JavaSMT Maven Web Example

This project shows how to use JavaSMT in a Maven-based web environment (WAR-based).
It includes a servlet that lists available solvers and a test case that solves a Sudoku puzzle.
The configuration in `pom.xml` handles the download and setup of native solver libraries (e.g., Z3, MathSAT5, CVC5) so they can be bundled into the WAR file.

## Prerequisites

* Java 17 or newer.
* Apache Maven.
* A servlet container like Apache Tomcat (e.g., version 10 or newer).
* Native solvers are only provided for **Linux x64** in this example. 
  Some solvers like Z3 and MathSAT5 also support Windows or ARM64 platform, if dependencies are adjusted in `pom.xml`.
  Java-only solvers (SMTInterpol, Princess) work on all platforms.
* When using Linux, please use Ubuntu 24.04 or newer, as we provide latest solver versions for GLIBC_2.33 or newer.

## Usage

### Compile and Build

Run the following to download dependencies and build the WAR file:
```bash
mvn clean package
```
Native libraries will be copied, renamed, and included in `WEB-INF/lib` of the generated WAR file.

### Run the Solver Overview Servlet

The WAR file can be deployed to your servlet container.
On Ubuntu with Tomcat, you can use the following steps:

1. Install Tomcat (required once):
   ```bash
   sudo apt install tomcat10
   sudo service tomcat10 start
   ```
2. Copy the WAR file to the `webapps` directory:
   ```bash
   sudo cp target/java-smt-web-example-VERSION.war /var/lib/tomcat10/webapps/
   ```
   Tomcat will automatically unpack the WAR file.
3. Open the following URL in your browser:
   `http://localhost:8080/java-smt-web-example-VERSION/SolverOverviewServlet`
   You should see a table of the available SMT solvers.


### Run the Solver Overview Servlet in a Docker Container

You can also run the servlet in a Docker container. Here’s how:
0. Compile and package the WAR file as described above.
1. Build the Docker image from `Dockerfile`:
   ```bash
   podman build -t java-smt-web-example .
   ```
2. Run the Docker container:
   ```bash
   podman run -p 8080:8080 java-smt-web-example
   ```
3. Access the servlet at `http://localhost:8080/SolverOverviewServlet` in your browser.


### Run Sudoku Test

The `SudokuTest` runs against all available solvers during the build process.

```bash
mvn test
```

## Project Structure

* `src/main/java/org/sosy_lab/SolverOverviewServlet.java`: Servlet implementation.
* `src/test/java/org/sosy_lab/java_smt_web_example/SudokuTest.java`: Parameterized JUnit test.
* `src/main/webapp/WEB-INF/web.xml`: Web application configuration.
* `pom.xml`: Maven configuration including dependency management and native library handling.

## Native Library Handling

JavaSMT backends often require native binaries. This project automates the following steps:
1. Download native libraries via Maven dependencies (using `classifier` and `type`).
2. Copy them to a temporary directory using `maven-dependency-plugin`.
3. Rename them (e.g., from `javasmt-solver-z3-libz3java-x64.so` to `libz3java.so`) using `maven-antrun-plugin` to match JavaSMT expectations.
4. Bundle the renamed libraries into `WEB-INF/lib` of the WAR file using `maven-war-plugin`.

For more details, see the [JavaSMT documentation](https://github.com/sosy-lab/java-smt).
