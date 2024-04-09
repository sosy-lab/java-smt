<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# JavaSMT

[![Build Status](https://gitlab.com/sosy-lab/software/java-smt/badges/master/pipeline.svg)](https://gitlab.com/sosy-lab/software/java-smt/pipelines)
[![Build Status on Windows](https://ci.appveyor.com/api/projects/status/uehe0fwa8bil8sha/branch/master?svg=true)](https://ci.appveyor.com/project/PhilippWendler/java-smt/branch/master)
![Test Coverage](https://gitlab.com/sosy-lab/software/java-smt/badges/master/coverage.svg)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)
[![Maven Central](https://maven-badges.herokuapp.com/maven-central/org.sosy-lab/java-smt/badge.svg)](https://maven-badges.herokuapp.com/maven-central/org.sosy-lab/java-smt)

JavaSMT is a common API layer for accessing various SMT solvers.
The API is optimized for performance (using JavaSMT has very little runtime
overhead compared to using the solver API directly), customizability
(features and settings exposed by various solvers should be visible through the
wrapping layer) and type-safety (it shouldn't be possible to add boolean terms
to integer ones at _compile_ time) sometimes at the cost of verbosity.

#### Quick links
[Getting Started](doc/Getting-started.md) |
[Documentation][JavaDoc] |
[Known Issues](doc/KnownIssues.md) |
[Documentation for Developers](doc/Developers.md) |
[Changelog](CHANGELOG.md) |
[Configuration Options][ConfigurationOptions]

#### References

- D. Baier, D. Beyer, and K. Friedberger.
  [**JavaSMT 3: Interacting with SMT Solvers in Java**](https://link.springer.com/content/pdf/10.1007/978-3-030-81688-9_9.pdf).
  In Proc. CAV, LNCS 12760, pages 1-13, 2021. Springer.
- E. G. Karpenkov, K. Friedberger, and D. Beyer.
  [**JavaSMT: A Unified Interface for SMT Solvers in Java**](https://www.sosy-lab.org/research/pub/2016-VSTTE.JavaSMT_A_Unified_Interface_For_SMT_Solvers_in_Java.pdf).
  In Proc. VSTTE, LNCS 9971, pages 139–148, 2016. Springer.

### Feature overview
JavaSMT can express formulas in the following theories:

 - Integer
 - Rational
 - Bitvector
 - Floating Point
 - Array
 - Uninterpreted Function
 - String and RegEx

The concrete support for a certain theory depends on the underlying SMT solver.
Only a few SMT solvers provide support for theories like Arrays, Floating Point, String or RegEx.

Currently JavaSMT supports several SMT solvers (see [Getting Started](doc/Getting-started.md) for installation):

| SMT Solver | Linux64 | Windows64 | MacOS | Description |
| --- |:---:|:---:|:---:|:--- |
| [Boolector](https://boolector.github.io/) | :heavy_check_mark: |  |  | a fast solver for bitvector logic, misses formula introspection |
| [CVC4](https://cvc4.github.io/) | :heavy_check_mark: |  |  |  |
| [CVC5](https://cvc5.github.io/) | :heavy_check_mark: |  |  | new! |
| [MathSAT5](http://mathsat.fbk.eu/) | :heavy_check_mark: | :heavy_check_mark: |  |  |
| [OpenSMT](https://verify.inf.usi.ch/opensmt) | :heavy_check_mark: |  |  | new! |
| [OptiMathSAT](http://optimathsat.disi.unitn.it/) | :heavy_check_mark: |  |  | based on MathSAT5, with support for optimization |
| [Princess](http://www.philipp.ruemmer.org/princess.shtml) | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: | Java-based SMT solver |
| [SMTInterpol](https://ultimate.informatik.uni-freiburg.de/smtinterpol/) | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: | Java-based SMT solver |
| [Yices2](https://yices.csl.sri.com/) | :heavy_check_mark: | [soon](https://github.com/sosy-lab/java-smt/pull/215) |  |  |
| [Z3](https://github.com/Z3Prover/z3) | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: | mature and well-known solver |

The following features are supported (depending on the used SMT solver):

 - Satisfiability checking
 - Quantifiers and quantifier elimination
 - Incremental solving with assumptions
 - Incremental solving with push/pop
 - Multiple independent contexts
 - Model generation
 - Interpolation, including tree and sequential structure
 - Formula transformation using built-in tactics
 - Formula introspection using visitors

We aim for supporting more important features, more SMT solvers, and more systems.
If something specific is missing, please [look for or file an issue](https://github.com/sosy-lab/java-smt/issues).

#### Multithreading Support
| SMT Solver | Concurrent context usage¹ | Concurrent prover usage² |
| --- |:---:|:---:|
| [Boolector](https://boolector.github.io/) | :heavy_check_mark: |  |
| [CVC4](https://cvc4.github.io/) | :heavy_check_mark: | :heavy_check_mark: |
| [CVC5](https://cvc4.github.io/) | :question: | |
| [MathSAT5](http://mathsat.fbk.eu/) | :heavy_check_mark: |  |
| [OpenSMT](https://verify.inf.usi.ch/opensmt) | :question: | |
| [OptiMathSAT](http://optimathsat.disi.unitn.it/) | :heavy_check_mark: |  |
| [Princess](http://www.philipp.ruemmer.org/princess.shtml) | :heavy_check_mark: |  |
| [SMTInterpol](https://ultimate.informatik.uni-freiburg.de/smtinterpol/) | :heavy_check_mark: |  |
| [Yices2](https://yices.csl.sri.com/) |  |  |
| [Z3](https://github.com/Z3Prover/z3) | :heavy_check_mark: |  |

Interruption using a [ShutdownNotifier][] may be used to interrupt a
a solver from any thread.
Formulas are translatable in between contexts/provers/threads using _FormulaManager.translateFrom()_.

¹ Multiple contexts, but all operations on each context only from a single thread.
² Multiple provers on one or more contexts, with each prover using its own thread.

#### Garbage Collection in Native Solvers
JavaSMT exposes an API for performing garbage collection on solvers
implemented in a native language.
As a native solver has no way of knowing whether the created formula
object is still referenced by the client application, this API is
necessary to avoid leaking memory.
Note that several solvers already support _hash consing_ and thus, there is
never more than one copy of an identical formula object in memory.
Consequently, if all created formulas are later re-used (or re-created)
in the application, it is not necessary to perform any garbage
collection at all.

##### Z3
The parameter `solver.z3.usePhantomReferences` may be used to control
whether JavaSMT will attempt to decrease references on Z3 formula
objects once they are no longer referenced.

##### MathSAT5
Currently we do not support performing garbage collection for MathSAT5.


## Getting started
Installation is possible via [Maven][Maven repository],
[Ivy][Ivy repository], or [manually][Manual Installation].
Please see our [Getting Started Guide](doc/Getting-started.md).

#### Usage
``` java
// Instantiate JavaSMT with SMTInterpol as backend (for dependencies cf. documentation)
try (SolverContext context = SolverContextFactory.createSolverContext(
        config, logger, shutdownNotifier, Solvers.SMTINTERPOL)) {
  IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

  // Create formula "a = b" with two integer variables
  IntegerFormula a = imgr.makeVariable("a");
  IntegerFormula b = imgr.makeVariable("b");
  BooleanFormula f = imgr.equal(a, b);

  // Solve formula, get model, and print variable assignment
  try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
    prover.addConstraint(f);
    boolean isUnsat = prover.isUnsat();
    assert !isUnsat;
    try (Model model = prover.getModel()) {
      System.out.printf("SAT with a = %s, b = %s", model.evaluate(a), model.evaluate(b));
    }
  }
}
```

## Authors

 - Project maintainers: [Karlheinz Friedberger][] and [Philipp Wendler][]
 - Former project maintainer: [George Karpenkov][]
 - Initial codebase, many design decisions: [Philipp Wendler][]
 - Contributions: [Daniel Baier][], [Thomas Stieglmaier][] and several others.

[ConfigurationOptions]: https://sosy-lab.github.io/java-smt/ConfigurationOptions.txt
[Manual Installation]: doc/Getting-started.md#manual-installation
[ShutdownNotifier]: https://sosy-lab.github.io/java-common-lib/api/org/sosy_lab/common/ShutdownNotifier.html
[JavaDoc]: https://sosy-lab.github.io/java-smt/
[George Karpenkov]: http://metaworld.me
[Philipp Wendler]: https://www.philippwendler.de/
[Thomas Stieglmaier]: https://stieglmaier.me/
[Karlheinz Friedberger]: https://www.sosy-lab.org/people/friedberger
[Daniel Baier]: https://www.sosy-lab.org/people/baier
[Ivy repository]: https://www.sosy-lab.org/ivy
[Maven repository]: https://mvnrepository.com/artifact/org.sosy-lab/java-smt
