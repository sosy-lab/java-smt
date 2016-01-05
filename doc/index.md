# Project Description & Philosophy

JavaSMT is a common API layer for accessing various SMT solvers.

It was born out of our experience integrating and using different SMT solvers
in [CPAchecker](http://cpachecker.sosy-lab.org/) project.
Consequently it is developed for medium to large software projects which may
benefit from SMT capabilities.
The API is optimized for transparency (it should be obvious what action is
performed when, the wrapping shouldn't be too "clever") and customizability
(features and settings exposed by various solvers should be visible through the
wrapping layer) sometimes at the cost of verbosity.
While the initial boylerplate may be discouraging for shorter scripts,
we have found it very useful for larger projects.

# Installation

Currently, `JavaSMT` supports two different installation methods:
automatic installation using Apache Ivy and manual using JARs.
We plan to add the packages to Maven Central soon.

### Automatic Installation using Ivy

If your build tool supports [Apache Ivy](http://ant.apache.org/ivy/) configured,
you can point it to [Sosy-Lab](http://www.sosy-lab.org/) Ivy
[repository](IvyRepository), which would automatically fetch
`JavaSMT` and all of its dependencies.

After the repository URL is configured, you only need to add the following
dependency:

```xml
<dependency org="org.sosy_lab" name="javasmt" rev="latest" />
```

### Manual Installation using JAR files

Alternatively, JARs for JavaSMT and its dependencies can be downloaded from our
[Ivy Repository](IvyRepository) manually.

## Using Solver Binaries

Solver binaries for native solvers (currently CVC4, Z3, MathSAT5 and
OptiMathSAT5) are downloaded automatically by Ivy.
We supply only one version of binaries: for 64-bit linux platforms
(tested on Ubuntu latest LTS).
To use the supplied binaries, they should either be copied or symlinked to
`lib/native/x86_64-linux` folder.

For other architectures, the binaries have to be copied to the architecture-specific
folder, see [NativeLibraries](NativeLibraries) documentation for details.

Note that solvers which run directly on JDK (currently Princess and SMTInterpol)
do not require any such configuration and work out of the box.

# Usage

## Getting Started

This is a small example to get started:

```java
int main(String[] args) {

    // SMT solvers often expose many different flags.
    // We populate them using the Configuration object,
    // which can be created either from .properties file or from
    // a command line.
    Configuration config = Configuration.fromCommandLine(args);

    // All interaction with the solver can be logged.
    LogManager logger = new LogManager();

    // Satisfiability queries often take a very long time.
    // For "graceful" interrupts we provide a shutdown notifier,
    // which can be used to either implement a timeout on a query,
    // or gracefully respond to Ctrl-C requests.
    ShutdownNotifier notifier = new ShutdownNotifier();

    // FormulaManager is a class wrapping a solver context.
    // All interactions with a solver are normally done through this class.
    FormulaManager manager = FormulaManagerFactory.createFormulaManager
        config, logger, notifier);

    Formula a = manager.createVariable(FormulaType.INTEGER, "a");

}
```

[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
[NativeLibraries]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/NativeLibraries.html
[Configuration]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/package-summary.html
[LogManager]: https://sosy-lab.github.io/java-common-lib/api/index.html?org/sosy_lab/common/configuration/package-summary.html
[FormulaManagerFactory]: http://sosy-lab.github.io/java-smt/api/org/sosy_lab/solver/FormulaManagerFactory.html
[IvyRepository]: http://www.sosy-lab.org/ivy
