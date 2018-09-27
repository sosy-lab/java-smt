# JavaSMT

[![Build Status](https://gitlab.com/sosy-lab/software/java-smt/badges/master/pipeline.svg)](https://gitlab.com/sosy-lab/software/java-smt/pipelines)
[![Build Status on Windows](https://ci.appveyor.com/api/projects/status/uehe0fwa8bil8sha/branch/master?svg=true)](https://ci.appveyor.com/project/PhilippWendler/java-smt/branch/master)
[![Code Quality](https://api.codacy.com/project/badge/Grade/94b27e1928034a4f9d91faad82a0b870)](https://www.codacy.com/app/PhilippWendler/java-smt?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=sosy-lab/java-smt&amp;utm_campaign=Badge_Grade)
[![Test Coverage](https://api.codacy.com/project/badge/Coverage/94b27e1928034a4f9d91faad82a0b870)](https://www.codacy.com/app/PhilippWendler/java-smt?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=sosy-lab/java-smt&amp;utm_campaign=Badge_Coverage)
[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)
[![Maven Central](https://maven-badges.herokuapp.com/maven-central/org.sosy-lab/java-smt/badge.svg)](https://maven-badges.herokuapp.com/maven-central/org.sosy-lab/java-smt)

JavaSMT is a common API layer for accessing various SMT solvers.
The API is optimized for performance (using JavaSMT has very little runtime
overhead compared to using the solver API directly), customizability
(features and settings exposed by various solvers should be visible through the
wrapping layer) and type-safety (it shouldn't be possible to add boolean terms
to integer ones at _compile_ time) sometimes at the cost of verbosity.

#### Quick links
[Getting Started](getting-started.md) |
[Documentation][JavaDoc] |
[Known Issues](KnownIssues.md) |
[Documentation for Developers](Developers.md) |
[Changelog](CHANGELOG.md) |
[Configuration Options](ConfigurationOptions.txt)

### Feature overview
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

#### Multithreading Support
All solvers support multithreading (MathSAT only since JavaSMT 1.0.1-164-gd14ed28),
provided that different threads use different contexts,
and _all_ operations on a single context are performed from a single thread.
Interruption using [ShutdownNotifier][] may be used to interrupt a
a solver from any thread.

#### Garbage Collection in Native Solvers
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

##### Z3
The parameter `solver.z3.usePhantomReferences` may be used to control
whether JavaSMT will attempt to decrease references on Z3 formula
objects once they are no longer referenced.

##### MathSAT5
Currently we do not support performing garbage collection for MathSAT5.


## Getting started
Installation is possible via [Maven][Maven repository], [Ivy][Ivy repository], or [manually][Manual Installation].  Please see our [Getting Started Guide](getting-started.md)

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

 - Project maintainers: [George Karpenkov][], [Karlheinz Friedberger][]
 - Initial codebase, many design decisions: [Philipp Wendler][]
 - Contributions: [Thomas Stieglmaier][] and others.
 
[Manual Installation]: getting-started.md
[JavaDoc]: https://sosy-lab.github.io/java-smt/
[George Karpenkov]: http://metaworld.me
[Philipp Wendler]: https://www.philippwendler.de/
[Thomas Stieglmaier]: https://stieglmaier.me/
[Karlheinz Friedberger]: https://www.sosy-lab.org/people/friedberger
[Ivy repository]: https://www.sosy-lab.org/ivy
[Maven repository]: https://mvnrepository.com/artifact/org.sosy-lab/java-smt