<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# Getting started
For existing code examples, please see our [examples][example code].

## Step 1: Install JavaSMT

### Automatic Installation using Ivy (preferred)

If your build tool supports fetching packages from [Apache Ivy](https://ant.apache.org/ivy/),
you can point it to [Sosy-Lab](https://www.sosy-lab.org/) [Ivy repository][],
which would automatically fetch `JavaSMT` and all of its dependencies.

After the repository URL is configured, you only need to add the following dependency:

```xml
<dependency org="org.sosy_lab" name="java-smt" rev="5.0.0" conf="runtime->runtime"/>
```

#### Architecture specification

JavaSMT includes native binaries for several SMT solvers and only installs for x64 architecture, by default.
Starting with version 5.0.?, JavaSMT also supports additional architectures, such as x64 and arm64.
For a full list of supported solvers and architectures, refer to the [Readme](../README.md).
You can configure and download dependencies for specific architectures, or even multiple architectures in parallel.
To specify an architecture, the Ivy configuration must recognize the `arch` attribute.
An example Ivy configuration for this setup can be found in the [Ivy settings](../build/ivysettings.xml) of JavaSMT.

Afterwards, you can use JavaSMT for other architectures with:

```xml
<dependency org="org.sosy_lab" name="java-smt" rev="5.0.?" conf="runtime->runtime-x64"/>
```

or

```xml
<dependency org="org.sosy_lab" name="java-smt" rev="5.0.?" conf="runtime->runtime-arm64"/>
```

Or specify a specific architecture for a solver directly:

```xml
<dependency org="org.sosy_lab" name="javasmt-solver-z3" rev="4.13.3" conf="runtime->solver-z3-arm64"/>
```

### Automatic Installation from Maven Central (possibly outdated)

If you use Maven/Gradle/SBT/etc to build your project, a dependency to JavaSMT
can be added using a single configuration item.

For Maven:

```xml
<dependency>
  <groupId>org.sosy-lab</groupId>
  <artifactId>java-smt</artifactId>
  <version>5.0.0-61-gea80187e</version>
</dependency>
```

Currently, only `SMTInterpol` and `Princess` are automatically fetched from Maven Central,
because they are written in Java and Scala, and thus are available on every machine.
Shared object for the solvers `MathSAT5` and `Z3` can be added by using additional dependencies (example for Linux):

```xml
    <!-- MathSAT5 has one dependency -->
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-mathsat5</artifactId>
      <version>5.6.5</version>
      <type>so</type>
    </dependency>

    <!-- Z3 has three dependencies -->
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-z3</artifactId>
      <version>4.8.10</version>
    </dependency>
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-z3</artifactId>
      <version>4.8.10</version>
      <type>so</type>
      <classifier>libz3</classifier>
    </dependency>
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-z3</artifactId>
      <version>4.8.10</version>
      <type>so</type>
      <classifier>libz3java</classifier>
    </dependency>
```

The XML snippets for other solvers available via Maven, such as `Boolector` and `CVC4`,
can be found in the [`POM file`](Example-Maven-Project/pom.xml) of our [`Example-Maven-Project`](Example-Maven-Project).

If you are not using Linux and we provide a solver binary for your system,
you might need to set the dependencies accordingly, e.g.,
change the type from `so` to `dll` (for Windows) or `dylib` (for MacOS).
You can lookup the required dependency files and filename extension in the [Ivy repository][].

Additionally you can add and configure some Maven plugins to load the libraries automatically
and place them in the correct directories when assembling your application.
The plugins copy all dependencies (including the solver binaries) to the target/dependency directory
and rename the libraries as required for automated loading.
A detailed explanation for these plugins is given in the [`Example-Maven-Project/pom.xml`](Example-Maven-Project/pom.xml).
For testing, you might need to add the dependency directory to the classpath for your test-engine.

Example:

```xml
<configuration>
  <argLine>-Djava.library.path=${project.build.directory}/dependency</argLine>
</configuration>
```

And finally configure the classpath for your jar-plugin:

```xml
<manifest>
  <addClasspath>true</addClasspath>
  <classpathPrefix>${project.build.directory}/dependency</classpathPrefix>
</manifest>
```

See [`Example-Maven-Project`](Example-Maven-Project) for more information and a working example.
See [`Example-Maven-Web-Project`](Example-Maven-Web-Project) for more information about a Dynamic-Web-Project runnable by Tomcat 9.

Shared object for _other solvers still need to be installed manually_:
see the section "Manual Installation" below.


### Manual Installation

JARs for JavaSMT and its dependencies can be downloaded from our [Ivy repository][] manually.
In order to perform the manual installation, the following steps should be followed:

 - The desired version has to be chosen.
   Latest version can be found by looking at the [Ivy index](https://www.sosy-lab.org/ivy/org.sosy_lab/java-smt/).
   **JavaSMT might not yet support the latest version on the solver's webpage,
   but only the latest version in the [Ivy index](https://www.sosy-lab.org/ivy/org.sosy_lab/java-smt/).**
 - Suppose the version `5.0.0` was chosen.
   Ivy description file [`ivy-5.0.0.xml`](https://www.sosy-lab.org/ivy/org.sosy_lab/java-smt/ivy-5.0.0.xml) can
   be consulted in order to determine all the files which should be fetched.
 - The artifacts tag specifies what files the release depends on.
   In the example case, those are `java-smt-5.0.0.jar` and (optionally)
   `java-smt-5.0.0-sources.jar`, located in the same directory.
 - Finally, the dependencies can be manually followed and resolved.
   E.g. in the example, Z3 version `4.13.3` is specified,
   which is described by the corresponding [XML](https://www.sosy-lab.org/ivy/org.sosy_lab/javasmt-solver-z3/ivy-4.13.3.xml)
   file, specifying what binaries should be fetched from the corresponding
   [directory](https://www.sosy-lab.org/ivy/org.sosy_lab/javasmt-solver-z3/).


### Binaries for Native Solvers

When using Ivy or Maven for installation on a 64-bit Linux platform,
solver binaries for native solvers are downloaded automatically, if available.
The [Readme](../README.md) contains a list of solvers and supported platforms.
Everything should work as is after installation.

Without Ivy or Maven you need to download and install the binaries manually as described above under [Manual Installation](#manual-installation).
You can either copy them into the directory of the JavaSMT JAR file,
or in a directory `../native/<arch>-<os>/` relative to the directory of the JAR file.
See [NativeLibraries][] documentation for more details on which path is searched.

We might not provide binaries for some platforms,
so you need to download or compile them for yourself, if supported by the SMT solver.
You can find the necessary steps for compiling and using solver binaries in [`lib/native/source/`](../lib/native/source/) and [`build`](../build).
Solvers which run directly on JDK (currently Princess and SMTInterpol)
do not require any configuration and work out of the box.

Currently, the support for newly integrated solvers like Boolector, CVC4, and Yices2 is limited.
We are working on supporting more solvers on more operating systems. A helping hand or feedback is also welcome.

## Step 2: Initialization
Below is a small example showing how to initialize the library using the entry point [SolverContextFactory][]:

```java
public class TestApp {
  public static void main(String[] args) throws InvalidConfigurationException {
    Configuration config = Configuration.fromCmdLineArguments(args);
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    // SolverContext is a class wrapping a solver context.
    // Solver can be selected either using an argument or a configuration option
    // inside `config`.
    SolverContext context = SolverContextFactory.createSolverContext(
        config, logger, shutdown.getNotifier(), Solvers.SMTINTERPOL);
  }
}
```

JavaSMT relies on three dependencies from the SoSy-Lab [Common][common] library.
These dependencies are:

 - [Configuration][]: JavaSMT accepts some configuration options
    and forwards options to the underlying SMT solver.
 - [LogManager][]: JavaSMT can be configured to provide extensive
    logging for the operations related to all SMT queries.
 - [ShutdownNotifier][] from a [ShutdownManager][]: Many SMT queries can take a very
    long time, potentially more than the user is willing to wait.
    What's more, for a solver implemented in the native code usual ways of
    interrupting a Java process (e.g. interrupt signal) would not work.
    Shutdown manager provides a solution to gracefully request termination,
    and JavaSMT and the solvers will try to respond to such requests as soon as possible.

Here is how to get an instance of these dependencies:

| Dependency | Dummy instance that does nothing | Regular instance |
| --- | --- | --- |
| [Configuration][] | [`Configuration.defaultConfiguration()`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/Configuration.html#defaultConfiguration--) | [`Configuration.fromCmdLineArguments(String[])`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/Configuration.html#fromCmdLineArguments-java.lang.String:A-) or [`Configuration.builder()...build()`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/Configuration.html#builder--) for more flexible definition of options (e.g., from `.properties` files) |
| [LogManager][] | [`LogManager.createNullLogManager()`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/log/LogManager.html#createNullLogManager--) | [`BasicLogManager.create(Configuration)`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/log/BasicLogManager.html#create-org.sosy_lab.common.configuration.Configuration-) for logging to the JDK logging API; for other logging frameworks just write a wrapper implementing [LogManager][] |
| [ShutdownNotifier][] | [`ShutdownNotifier.createDummy()`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html#createDummy--) | [`ShutdownManager.create().getNotifier()`](https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownManager.html#create--) |

## Step 3: Solving Constraints

Once the [SolverContext][] is initialized, we can start posing queries to the
solver.
In this example, we want to find a satisfying example for a constraint
over integers `a`, `b` and `c`:

```
a + b = c \/ a + c = 2 * b
```

Creating the required constraint is straightforward:

```java
    // Assume we have a SolverContext instance.
    FormulaManager fmgr = context.getFormulaManager();

    BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
    IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();

    IntegerFormula a = imgr.makeVariable("a"),
                   b = imgr.makeVariable("b"),
                   c = imgr.makeVariable("c");
    BooleanFormula constraint = bmgr.or(
        imgr.equal(
            imgr.add(a, b), c
        ),
        imgr.equal(
            imgr.add(a, c), imgr.multiply(imgr.makeNumber(2), b)
        )
    );
```

Note the types of the formulas: `IntegerFormula` and `BooleanFormula`.
Using different classes for different types of formulas adds additional
guarantees at compile-time: unless an unsafe cast is used, it is impossible
to e.g. add an integer to a boolean using JavaSMT API.

Once the constraint is generated, we can solve it and get the model:

```java
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(constraint);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        Model model = prover.getModel();
      }
    }
```

Try-with-resources syntax will dispose of the prover once solving is finished.

Once the model is obtained we can get values from it either by iterating
through all of the returned data, or by querying for the variables we need:

```java
    BigInteger value = model.evaluate(a);
```

For further information, look at our full example [HoudiniApp][], [other examples][example code], or at the [JavaDoc][].

[SolverContext]: https://sosy-lab.github.io/java-smt/api/org/sosy_lab/java_smt/api/SolverContext.html
[SolverContextFactory]: https://sosy-lab.github.io/java-smt/api/org/sosy_lab/java_smt/SolverContextFactory.html
[ShutdownManager]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownManager.html
[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
[NativeLibraries]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/NativeLibraries.html
[Configuration]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/package-summary.html
[LogManager]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/log/LogManager.html
[common]: https://github.com/sosy-lab/java-common-lib
[HoudiniApp]: https://github.com/sosy-lab/java-smt/blob/master/src/org/sosy_lab/java_smt/example/HoudiniApp.java
[JavaDoc]: https://sosy-lab.github.io/java-smt/
[example code]: /src/org/sosy_lab/java_smt/example
[Ivy repository]: https://www.sosy-lab.org/ivy
