# JavaSMT

[![Build Status](https://api.travis-ci.org/sosy-lab/java-smt.svg?branch=master "Build Status")](https://travis-ci.org/sosy-lab/java-smt)
[![Build Status on Windows](https://ci.appveyor.com/api/projects/status/uehe0fwa8bil8sha/branch/master?svg=true)](https://ci.appveyor.com/project/PhilippWendler/java-smt/branch/master)
[![Code Quality](https://api.codacy.com/project/badge/Grade/94b27e1928034a4f9d91faad82a0b870)](https://www.codacy.com/app/PhilippWendler/java-smt?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=sosy-lab/java-smt&amp;utm_campaign=Badge_Grade)
[![Test Coverage](https://api.codacy.com/project/badge/Coverage/94b27e1928034a4f9d91faad82a0b870)](https://www.codacy.com/app/PhilippWendler/java-smt?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=sosy-lab/java-smt&amp;utm_campaign=Badge_Coverage)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)
[![Maven Central](https://maven-badges.herokuapp.com/maven-central/org.sosy-lab/java-smt/badge.svg)](https://maven-badges.herokuapp.com/maven-central/org.sosy-lab/java-smt)

Unified Java API for SMT solvers.

# Project Description & Philosophy

JavaSMT is a common API layer for accessing various SMT solvers.
It was published as a [paper](http://doi.org/10.1007/978-3-319-48869-1_11) at [VSTTE 2016](https://www.cs.toronto.edu/~chechik/vstte16/).

It was created out of our experience integrating and using different SMT solvers
in the [CPAchecker][] project.
The library is developed for medium to large software projects which
require access to SMT solvers.
The API is optimized for performance (using JavaSMT has very little runtime
overhead compared to using the solver API directly), customizability
(features and settings exposed by various solvers should be visible through the
wrapping layer) and type-safety (it shouldn't be possible to add boolean terms
to integer ones at _compile_ time) sometimes at the cost of verbosity.

## Supported Solvers

Currently, we support the following SMT solvers:

 - [Z3](https://github.com/Z3Prover/z3)
 - [MathSAT](http://mathsat.fbk.eu/)
 - [OptiMathSAT](http://optimathsat.disi.unitn.it/)
 - [SMTInterpol](https://ultimate.informatik.uni-freiburg.de/smtinterpol/)
 - [Princess](http://www.philipp.ruemmer.org/princess.shtml)

Support for CVC4 is planned in the near future (cf. [#2](https://github.com/sosy-lab/java-smt/issues/2)).

## Supported Features

JavaSMT can express formulas in the following theories:

 - Integer
 - Rational
 - Bitvector
 - Floating point
 - Array
 - Uninterpreted Function

The following features are supported:

 - Satisfiability checking
 - Quantifiers and quantifier elimination
 - Incremental solving with assumptions
 - Incremental solving with push/pop
 - Multiple independent contexts
 - Model generation
 - Interpolation, including tree and sequential
 - Formula transformation using built-in tactics
 - Formula introspection using visitors

### Multithreading Support

All solvers support multithreading (MathSAT only since JavaSMT 1.0.1-164-gd14ed28),
provided that different threads use different contexts,
and _all_ operations on a single context are performed from a single thread.
Interruption using [ShutdownNotifier][] may be used to interrupt a
a solver from any thread.

### Garbage Collection in Native Solvers

JavaSMT exposes an API for performing garbage collection on solvers
implemented in a native language.
As a native solver has no way of knowing whether the created formula
object is still referenced by the client application, this API is
necessary to avoid leaking memory.
Note that due to the _hash consing_ usage inside the solvers, there is
never more than one copy of an identical formula object in memory.
Consequently, if all created formulas are later re-used (or re-created)
in the application, it is not necessary to perform any garbage
collection at all.

#### Z3

The parameter `solver.z3.usePhantomReferences` may be used to control
whether JavaSMT will attempt to decrease references on Z3 formula
objects once they are no longer referenced.

#### MathSAT5

Currently we do not support performing garbage collection for MathSAT5.

# Installation

### Automatic Installation from Maven Central

If you use Maven/Gradle/SBT/etc to build your project, a dependency to JavaSMT
can be added using a single configuration item.

For Maven:

```xml
<dependency>
  <groupId>org.sosy-lab</groupId>
  <artifactId>java-smt</artifactId>
  <version>1.0.1</version>
</dependency>
```

Currently, only SMTInterpol is automatically fetched from Maven Central,
and shared object for other solvers would have to be installed manually:
see the section "Manual Installation" below.

### Automatic Installation using Ivy

If your build tool supports fetching packages from
[Apache Ivy](https://ant.apache.org/ivy/),
you can point it to [Sosy-Lab](https://www.sosy-lab.org/) [Ivy repository][], which would automatically fetch
`JavaSMT` and all of its dependencies.

After the repository URL is configured, you only need to add the following
dependency:

```xml
<dependency org="org.sosy_lab" name="javasmt" rev="0.60" />
```

### Manual Installation

JARs for JavaSMT and its dependencies can be downloaded from our
[Ivy repository][] manually.
In order to perform the manual installation, the following steps should
be followed:

 - The desired version has to be chosen.
   Latest version can be found by looking at the [Ivy index](https://www.sosy-lab.org/ivy/org.sosy_lab/javasmt/).
 - Suppose the version `1.0.1` was chosen.
   Ivy description file [`ivy-1.0.1.xml`](https://www.sosy-lab.org/ivy/org.sosy_lab/javasmt/ivy-1.0.1.xml) can
   be consulted in order to determine all the files which should be fetched.
 - The artifacts tag specifies what files the release depends on.
   In the example case, those are `javasmt-1.0.1.jar` and (optionally)
   `javasmt-1.0.1-sources.jar`, located in the same directory.
 - Finally, the dependencies can be manually followed and resolved.
   E.g. in the example, Z3 version `z3-4.4.1-1394-gd12efb6` is specified,
   which is described by the corresponding [XML](https://www.sosy-lab.org/ivy/org.sosy_lab/javasmt-solver-z3/ivy-z3-4.4.1-1558-gf96cfea.xml)
   file, specifying what binaries should be fetched from the corresponding
   [directory](https://www.sosy-lab.org/ivy/org.sosy_lab/javasmt-solver-z3/).

### Binaries for Native Solvers (MathSAT and Z3)

When using Ivy for installation on a 64-bit Linux platform,
solver binaries for native solvers are downloaded automatically.
Everything should work as is after installation.

Without Ivy you need to download and install the binaries manually as described above
under [Manual Installation](README.md#manual-installation).
You can either copy them into the directory of the JavaSMT JAR file,
or in a directory `../native/<arch>-<os>/` relative to the directory of the JAR file.
See [NativeLibraries][] documentation for more details on which path is searched.

For systems other than 64-bit Linux (e.g., Windows, or 32-bit systems)
we do not provide binaries so you need to compile them for yourself.
For Z3, [download it](https://github.com/Z3Prover/z3)
and build it with the flags `--staticlib --java --git-describe` according to its documentation.
Then install the files `libz3.(so|dll)` and `libz3java.(so|dll)` as described above.
You might also experiment with using its [latest binary release](https://github.com/Z3Prover/z3/releases),
though we recommend the latest git version of Z3 due to its large number of fixes and improvements.
In order to compile MathSAT binaries,
see the comments in the [`lib/native/source/libmathsat5j/compile.sh`](lib/native/source/libmathsat5j/compile.sh)
script.

Solvers which run directly on JDK (currently Princess and SMTInterpol)
do not require any configuration and work out of the box.

# Quickstart Guide

## Initialization

Below is a small example showing how to initialize the library using the entry point [SolverContextFactory][]:

```java
package org.sosy_lab.java_smt.test;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

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

## Solving Constraints

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
guarantees at compile-time: unless and unsafe cast is used, it is impossible
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

For further information, look at our full example [HoudiniApp][], or at the [JavaDoc][].

## Further Documentation

 - [JavaDoc][]
 - [ConfigurationOptions][]
 - [Changelog](https://github.com/sosy-lab/java-smt/blob/master/CHANGELOG.md)
 - [Documentation For Developers](https://github.com/sosy-lab/java-smt/blob/master/Developers.md)
 - [Known Issues](https://github.com/sosy-lab/java-smt/blob/master/KnownIssues.md)

## Authors

 - Project maintainers: [George Karpenkov][], [Karlheinz Friedberger][]
 - Initial codebase, many design decisions: [Philipp Wendler][]
 - Contributions: [Thomas Stieglmaier][] and others.

### Additional Acknowledgements

 - Profiled with [jProfiler][] Java Profiler.

[CPAchecker]: https://cpachecker.sosy-lab.org/
[jProfiler]: https://www.ej-technologies.com/products/jprofiler/overview.html
[common]: https://github.com/sosy-lab/java-common-lib
[ShutdownManager]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownManager.html
[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
[NativeLibraries]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/NativeLibraries.html
[Configuration]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/package-summary.html
[BasicLogManager]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/log/BasicLogManager.html
[LogManager]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/log/LogManager.html
[SolverContext]: https://sosy-lab.github.io/java-smt/api/org/sosy_lab/java_smt/api/SolverContext.html
[SolverContextFactory]: https://sosy-lab.github.io/java-smt/api/org/sosy_lab/java_smt/SolverContextFactory.html
[HoudiniApp]: https://github.com/sosy-lab/java-smt/blob/master/src/org/sosy_lab/java_smt/example/HoudiniApp.java
[JavaDoc]: https://sosy-lab.github.io/java-smt/
[ConfigurationOptions]: https://sosy-lab.github.io/java-smt/ConfigurationOptions.txt
[Ivy repository]: https://www.sosy-lab.org/ivy
[George Karpenkov]: http://metaworld.me
[Philipp Wendler]: https://www.philippwendler.de/
[Thomas Stieglmaier]: https://stieglmaier.me/
[Karlheinz Friedberger]: https://www.sosy-lab.org/people/friedberger
