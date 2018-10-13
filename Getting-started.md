# Getting started
For existing code examples, please see our [examples][example code].

## Step 1: Install JavaSMT
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

If your build tool supports fetching packages from [Apache Ivy](https://ant.apache.org/ivy/), you can point it to [Sosy-Lab](https://www.sosy-lab.org/) [Ivy repository][], which would automatically fetch `JavaSMT` and all of its dependencies.

After the repository URL is configured, you only need to add the following dependency:

```xml
<dependency org="org.sosy_lab" name="javasmt" rev="0.60" />
```

### Manual Installation

JARs for JavaSMT and its dependencies can be downloaded from our [Ivy repository][] manually. In order to perform the manual installation, the following steps should be followed:

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

When using Ivy for installation on a 64-bit Linux platform, solver binaries for native solvers are downloaded automatically. Everything should work as is after installation.

Without Ivy you need to download and install the binaries manually as described above under [Manual Installation](manual-installation).
You can either copy them into the directory of the JavaSMT JAR file,
or in a directory `../native/<arch>-<os>/` relative to the directory of the JAR file.
See [NativeLibraries][] documentation for more details on which path is searched.

For systems other than 64-bit Linux (e.g., Windows, or 32-bit systems)
we do not provide binaries so you need to download or compile them for yourself.
For [Z3][], download either the [official binaries](https://github.com/Z3Prover/z3/releases)
or build it with the flags `--java --git-describe` according to its documentation.
Then install the files `libz3.(so|dll)` and `libz3java.(so|dll)` as described above.
In order to compile MathSAT binaries,
see the comments in the [`lib/native/source/libmathsat5j/compile.sh`](lib/native/source/libmathsat5j/compile.sh)
script.

Solvers which run directly on JDK (currently Princess and SMTInterpol)
do not require any configuration and work out of the box.

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
