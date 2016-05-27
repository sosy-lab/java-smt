# JavaSMT

[![Build Status](https://api.travis-ci.org/sosy-lab/java-smt.svg?branch=master "Build Status")](https://travis-ci.org/sosy-lab/java-smt)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](http://www.apache.org/licenses/LICENSE-2.0)

Unified Java API for SMT solvers.

# Project Description & Philosophy

JavaSMT is a common API layer for accessing various SMT solvers.

It was created out of our experience integrating and using different SMT solvers
in [CPAchecker](http://cpachecker.sosy-lab.org/) project.
The library is developed for medium to large software projects which
require access to SMT solvers.
The API is optimized for performance (using JavaSMT has very little runtime
overhead compared to using the solver API directly), customizability
(features and settings exposed by various solvers should be visible through the
wrapping layer) and type-safety (it shouldn't be possible to add boolean terms
to integer ones at _compile_ time) sometimes at the cost of verbosity.

# Installation

### Automatic Installation from Maven Central

If you use Maven/Gradle/SBT/etc to build your project, a dependency to JavaSMT
can be added using a single configuration item.

For Maven:

```xml
<dependency>
  <groupId>org.sosy-lab</groupId>
  <artifactId>java-smt</artifactId>
  <version>0.51</version>
</dependency>
```

Or for Gradle:

```
dependencies {
  compile 'org.sosy-lab:common:0.51'
}
```

Currently, only SMTInterpol is automatically fetched from Maven Central,
and other solvers would have to be installed manually.

### Automatic Installation using Ivy

If your build tool supports fetching packages from
[Apache Ivy](http://ant.apache.org/ivy/),
you can point it to [Sosy-Lab](http://www.sosy-lab.org/) Ivy
[repository](IvyRepository), which would automatically fetch
`JavaSMT` and all of its dependencies.

After the repository URL is configured, you only need to add the following
dependency:

```xml
<dependency org="org.sosy_lab" name="javasmt" rev="latest.integration" />
```

### Manual Installation using JAR files

Alternatively, JARs for JavaSMT and its dependencies can be downloaded from our
[Ivy Repository](IvyRepository) manually:

<!-- TODO: guide for fetching solver binaries/etc-->

## Binaries for Native Solvers (MathSAT and Z3)

Solver binaries for native solvers are downloaded automatically by Ivy.
We supply binaries only for 64-bit linux platforms
(tested on Ubuntu latest LTS).
If you have this architecture, then (hopefully) everything should work as is after
installation.

If you require native solvers on a different platform, then you can copy the
`.so` binaries manually to the folder in `lib/native` corresponding to your
architecture.
See [NativeLibraries](NativeLibraries) documentation for more details.

Solvers which run directly on JDK (currently Princess and SMTInterpol)
do not require any configuration and work out of the box.

# Usage

## Initialization

Below is a small example showing how to initialize the library:

```java
package org.sosy_lab.solver.test;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverContextFactory;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.SolverContext;

public class TestApp {
  public static void main(String[] args) throws InvalidConfigurationException {
    Configuration config = Configuration.fromCmdLineArguments(args);
    LogManager logger = new BasicLogManager(config);
    ShutdownNotifier notifier = ShutdownManager.create().getNotifier();

    // SolverContext is a class wrapping a solver context.
    // Solver can be selected either using an argument or a configuration option
    // inside `config`.
    SolverContext context = SolverContextFactory.
        createSolverContext(config, logger, notifier, Solvers.SMTINTERPOL);
  }
}
```

JavaSMT relies on three dependencies from the SoSy-Lab [common](common) library.
These dependencies are:

 - [Configuration](Configuration): SMT solvers expose many different
    configuration options, and using the configuration object they can be
    easily populated by the client, either from the command line or from 
    `.properties` file.
 - [LogManager](LogManager): JavaSMT can be configured to provide extensive
    logging for the operations related to all SMT queries.
    If you already use your own logging framework, you just have to create a
    wrapper implementing `LogManager` interface.
 - [ShutdownNotifier](ShutdownNotifier): Many SMT queries can take a very
    long time, potentially more than the user is willing to wait.
    What's more, for a solver implemented in the native code usual ways of
    interrupting a Java process (e.g. interrupt signal) would not work.
    Shutdown notifier provides a solution to handle interrupts gracefully,
    without having to resort to `kill -9` command.

## Quickstart guide

Once the formula manager is initialized, we can start posing queries to the
solver.
In this example, we want to find a satisfying example for a constraint
over integers `a`, `b` and `c`:

```
a + b = c \/ a + c = 2 * b
```

Creating the required constraint is straghtforward:

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

## Known Solver Issues

### SMTInterpol

 - SMTInterpol does not support multiple concurrent stacks under the same context.

### Z3

 - Z3 interpolation procedure might require a large amount of stack memory.
If you get segmentation fault on interpolation, try increasing the stack size 
with the parameter `-Xss` for your Java program or `-stack` for CPAchecker.

## Authors

 - Project maintainer: George Karpenkov
 - Initial codebase, many design decisions: Philipp Wendler
 - Contributions: Thomas Stieglmaier, Karlheinz Friedberger

## Further Documentation

 - [JavaDoc documentation](http://sosy-lab.github.io/java-smt/)

[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
[NativeLibraries]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/NativeLibraries.html
[Configuration]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/package-summary.html
[LogManager]: https://sosy-lab.github.io/java-common-lib/api/index.html?org/sosy_lab/common/configuration/package-summary.html
[FormulaManagerFactory]: http://sosy-lab.github.io/java-smt/api/org/sosy_lab/solver/FormulaManagerFactory.html
[IvyRepository]: http://www.sosy-lab.org/ivy
