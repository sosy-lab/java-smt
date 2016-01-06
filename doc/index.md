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
do not require any such configuration and work out of the box.

# Usage

## Initialization

Below is a small example showing how to initialize the library:

```java
int main(String[] args) {

    Configuration config = Configuration.fromCommandLine(args);
    LogManager logger = new LogManager();
    ShutdownNotifier notifier = new ShutdownNotifier();

    // FormulaManager is a class wrapping a solver context.
    // All interactions with a solver are normally done through this class.
    FormulaManager manager = FormulaManagerFactory.createFormulaManager
        config, logger, notifier);
}
```

JavaSMT relies on three dependencies from the SoSy-Lab [common](common) library.
These dependencies are:

 - [Configuration](Configuration) - SMT solvers expose many different
    configuration options, and using the configuration object they can be
    easily populated by the client, either from the command line or from 
    `.properties` file.
 - [LogManager](LogManager) 

As shown above, [Configuration](Configuration), [LogManager](LogManager)


## Usage

Once the formula manager is initialized, we can start posing queries to the
solver.

```java
// Assume we have a FormulaManager instance.
BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();

BooleanFormula constraint = 

```


[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
[NativeLibraries]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/NativeLibraries.html
[Configuration]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/configuration/package-summary.html
[LogManager]: https://sosy-lab.github.io/java-common-lib/api/index.html?org/sosy_lab/common/configuration/package-summary.html
[FormulaManagerFactory]: http://sosy-lab.github.io/java-smt/api/org/sosy_lab/solver/FormulaManagerFactory.html
[IvyRepository]: http://www.sosy-lab.org/ivy
