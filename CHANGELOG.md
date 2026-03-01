<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# JavaSMT ChangeLog

## JavaSMT 6.0.0

#### Note: Version 6 will be the last mayor release for Java 11. We will move to Java 17 soon after and aim to subsequently adopt Java 21 still in 2026.

#### We plan to resume our regular updating policy again, providing more small updates more regularly.

### Breaking Changes
- Visitation of quantified formulas has been reworked due to inconsistencies in regard to bound-variables:
    - `visitBoundVariable()` has been deprecated due to solver specific inconsistencies.
    - a combination of `visitQuantifier` (for the whole quantified formula) and `visitAtom` (for variables in the body) can be used instead. This provides consistent behavior in all solvers.
- Many API calls in the `Model` and `ProverEnvironment` now throw `SolverException` and `InterruptedException`, as some solvers can throw these exceptions when executing the changed operations. MathSAT5 now throws a `SolverException` in cases in which model generation fails when requesting a model, instead of the previous `IllegalArgumentException`. Warning: `Model.iterator()` may throw the checked exceptions SolverException and InterruptedException although these exceptions are not declared with throws due to API restrictions.
- Floating-Point theory, `FloatingPointNumber`, and `FloatingPointType` have been reworked:
    - We now handle floating-point precisions as defined in the SMTLIB2 standard https://smt-lib.org/theories-FloatingPoint.shtml, i.e. output shows them now with the hidden bit included in the mantissa. Related documentation has been updated and extended to explain expected in- and output, i.e. `FloatingPointType.toSMTLIBString()`, `FloatingPointType.toString()`, and `FloatingPointType.fromString()`.
    - API has been added to discern mantissas with hidden bit, from mantissas without hidden bit. The old API, implicitly expecting a mantissa without hidden bit, has been deprecated. E.g. `FloatingPointType.getMantissaSize()` has been deprecated, while `FloatingPointType.getMantissaSizeWithHiddenBit()` and `FloatingPointType.getMantissaSizeWithoutHiddenBit()` have been added.
    - `FloatingPointNumber`s are now constructed using `FloatingPointType`, similar to how
      `FloatingPointFormula`s are constructed.
    - Public constants for single and double floating-point precisions that did not specify whether their mantissa includes the hidden bit have been deprecated, and new constants with more precise naming have been added.
- Floating-Point rounding-mode has also been reworked: 2 methods have been added to `FloatingPointFormulaManager` to allow access to rounding-mode formulas, i.e. `FloatingPointRoundingModeFormula`, formula representing a rounding mode for floating-point operations.
    - The old rounding-modes, `FP_ROUND_EVEN`, `FP_ROUND_AWAY`, `FP_ROUND_POSITIVE`, `FP_ROUND_NEGATIVE`, and `FP_ROUND_ZERO`, have been removed from `FunctionDeclarationKind`.
    - Use `FloatingPointFormulaManager.fromRoundingModeFormula()` to get the rounding mode of a `FloatingPointRoundingModeFormula`, and `FloatingPointFormulaManager.makeRoundingMode()` to create new `FloatingPointRoundingModeFormula`s.
    - The rounding-modes can now be accessed via `FloatingPointRoundingMode.getRoundingMode()`, but have been renamed: `FP_ROUND_AWAY` to `NEAREST_TIES_AWAY`, `FP_ROUND_AWAY` to `NEAREST_TIES_TO_EVEN`, `FP_ROUND_NEGATIVE` to `TOWARD_NEGATIVE`, `FP_ROUND_POSITIVE` to `TOWARD_POSITIVE`, and `FP_ROUND_ZERO` to `TOWARD_ZERO`.
- Boolector: (broken) support for quantified formulas has been removed.
- Unsat-core over assumptions generation now always requires the correct option `ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS`. 
  It was possible to use `ProverOptions.GENERATE_UNSAT_CORE` for unsat-core over assumption generation in MathSAT5 before.

### Solver updates
- Updated CVC5 from version 1.0.5 to daily release version 2026-02-26-d22638a (2 days 
  after version 1.3.3)
- Updated MathSAT5 from version 5.6.10 to 5.6.15
- Updated OptiMathSAT from version 1.7.1 to 1.7.3
- Updated Z3 from version 4.12.5 to 4.15.4
- Updated Bitwuzla from version 0.4.0 to 0.8.2
- Updated OpenSMT2 from version 2.6.0 to 2.9.0

### New Additions
- NEW SOLVER: Z3 (version 4.5.0) with interpolation support has been added as an solver, and can be used by choosing `Solvers.Z3_WITH_INTERPOLATION`. This version is distinct from the up-to-date version of Z3 (without interpolation support). This is currently experimental and still being worked on! Also, since this version of Z3 is more than 10 years old, it does not benefit from updates and developments in Z3 since then.
- OpenSMT2: options to specify a wanted interpolation technique (e.g. `interpolation.algorithm.lraTheory`), as well as interpolant simplification (`interpolation.simplificationLevel`) has been added.
- CVC5: SMTLIB2 parsing support has been added.
- CVC4/5: added support for bitvector to IEEE 754 floating-point number conversion with `FloatingPointManager.fromIeeeBitvector()`.
- Princess: support for the theory of Reals has been added.
- Princess: support for array models with multiple indices has been added.
- Princess: support for String theory has been added by incorporating Ostrich (version 2.0) into it.
- Yices2: support for quantified formulas has been added.
- String theory now supports Integer to code point and code point to Integer conversion (newly added methods: `StringFormulaManager.toCodePoint()` and `StringFormulaManager.fromCodePoint()`).
- Bitvector rotation support has been added to the formula visitor.
- Yices2: support for the theory of arrays has been added.
- String theory: Clarified that Strings used in the `StringFormulaManager` API are indeed Java Strings and may contain Unicode characters. Escape sequences like `\u0020` will not be translated automatically. Use `AbstractStringFormulaManager.escapeUnicodeForSmtlib()` and `AbstractStringFormulaManager.unescapeUnicodeForSmtlib()` to handle escape sequences when translating from/to SMT/SMTLIB2.
- Added `FormulaManager.makeEqual()` and `FormulaManager.makeDistinct()` as a more general way of creating equality (= ...) and distinct (distinct ...) formulas. The new methods are provided in addition of existing, theory specific, methods such as `IntegerFormulaManager.equal()` or `BitvectorFormulaManager.distinct()`. The API allows for an arbitrary number of arguments. The type of the arguments must match, except for formulas over Integer and Real theories, which may be mixed.
- Multi-assertion SMTLIB2 parsing has been added and can be used via `FormulaManager.parseAll()`.

### Updates
- Documentation for `unsatCoreOverAssumptions()` has been updated to reflect that it calls `isUnsatOverAssumptions()` automatically, 
  and does not require a call to `isUnsat()` or `isUnsatOverAssumptions()` directly preceding it.
- We now ensure that all model generating API (i.e. `getModel()`, `lower()`, and `upper()`) is only
  ever used directly after SAT has been returned by a solver. This ensures that no outdated models are retrieved.
  All value assignments of a new model are now automatically cached for all solvers in the first call to `getModel()`.
  Cached models are cleaned up automatically.
- Memory leaks in CVC5 and Bitwuzla have been fixed.
- Model generation in CVC5 and Bitwuzla has been optimized and should now be faster.
- We now support multiple architectures for solver binaries, allowing us to support ARM64 architectures in addition to x64 architectures. The following pre-build solver binaries are now available for ARM64 in our dependency system:
    - Linux ARM64: Bitwuzla, MathSAT5, CVC5, OpenSMT2, Princess, SMTInterpol, Z3, and Z3_WITH_INTERPOLATION
    - Windows ARM64: CVC5, Princess, SMTInterpol, Z3
    - MacOS ARM64: CVC5, Princess, SMTInterpol, Z3
- Model generation: to avoid possible solver inconsistencies; value-assignments are now always computed up-front, i.e. when a model is requested for a particular query in a `ProverEnvironment` after a SAT check for the first time, and invalidated once the underlying context of its `ProverEnvironment` is changed.
- Model generation: nested array support has been improved for Z3, CVC5, CVC4, Yices2, and Bitwuzla.
- SMTLIB2 parsing consistency in general (for all solvers) has been improved.
- Z3: a SEGFAULT caused by `IntegerFormulaManager.makeNumber()` for Integer theory has been fixed.
- CVC5: interpolation support has been improved.
- Separation-Logic: general improvements in the usability of the theory, as well as improved and extended documentation.
- MathSAT5: support for Integer theory modulo has been added.
- String theory: empty String ranges in `StringFormulaManager.range()` are now supported.
- `FunctionDeclarationKind`s used in the formula visitor have been extended with cases needed for conversion between bitvector and integer terms.


## JavaSMT 5.0.1

This patch release improves documentation and brings smaller improvements for CVC5.

## JavaSMT 5.0.0

This major release brings support for the SMT solver Bitwuzla (version 0.4.0), some bugfixes,
and includes several changes in the API.

### New features and breaking changes:
- User propagation can be used to provide a strategy when solving satisfiability (only Z3).
- Array theory supports the creation of constant arrays, e.g., specifying a default value for all indices.
- Bitvector theory provides rotation and improved modulo/remainder operations.
- Floating-point theory has better model evaluation.

### Updated solvers:
- Bitwuzla 0.4.0
- OpenSMT 2.6.0
- Z3 4.12.5

We slowly abandon Ubuntu 18.04 as build platform and will use Ubuntu 22.04 in the future. 

## JavaSMT 4.1.1

This patch release brings small fixes for Z3 and MathSAT.

## JavaSMT 4.1.0

This release brings support for the SMT solver OpenSMT (version 2.5.2).

## JavaSMT 4.0.3

This release contains updates for several dependencies.

## JavaSMT 4.0.2

This patch release improves documentation and updates the dependency for our Yices2 component.
We skip version 4.0.1 which was internally used for releasing the Yices2 component.

## JavaSMT 4.0.0

This major release comes with several updated solvers and dependencies,
a new (potentially faster) evaluator for models,
and support for the theory of enumerations (domains of fixed size).

### Breaking changes:
 - The push-method in ProverEnvironments can throw InterruptedExceptions.
 - Model evaluation supports enumeration theory.
 - Direct construction ArrayFormulaType was replaced with a static building method.

### Updated solvers:
 - MathSAT 5.6.10
 - Z3 4.12.2
 - CVC5 1.0.5

## JavaSMT 3.14.3

This patch release updates SMTInterpol to version 2.5-1242-g5c50fb6d.

## JavaSMT 3.14.2

This patch release brings small bugfixes for String theory.
We also include the brand-new bindings for the solver CVC5.

## JavaSMT 3.14.1

This patch release brings small bugfixes and improved documentation for formula visitation.

## JavaSMT 3.14.0

This minor release comes a new method 'allChar' in String theory
and brings with a smaller bugfix for formula visitation.

## JavaSMT 3.13.3

This patch release comes with a smaller bugfix for String-theory formulas in Z3.

## JavaSMT 3.13.2

This patch release comes with some updated solvers and some smaller bugfixes.

### Updated solvers:
 - JavaSMT 2.5-1147-g108647d8
 - Z3 4.10.1

## JavaSMT 3.13.1

This patch release contains with several smaller fixes for the integration of SMTInterpol and Princess.

## JavaSMT 3.13.0

This release comes with several bugfixes, e.g.,
we improved DIV and MOD operations in Integer theory.

### Updated solvers:
 - MathSAT 5.6.8
 - Princess 2022-07-01
 - Z3 4.8.17

### Breaking change:
The public API for FloatingPointManager was changed to support conversion
of FloatingPoint to signed and unsigned Bitvectors.

## JavaSMT 3.12.0

This release comes with an initial support for String theory for SMT solvers like Z3 and CVC4.
Now, JavaSMT provides statistics on the solving process, depending on the used SMT solver.
And we include several bugfixes and internal cleanup.

### Breaking change:
The public API was enriched with new methods to retrieve a StringFormulaManager and statistics.

## JavaSMT 3.11.0

This release comes with support for multiple prover stacks in SMTInterpol.

### Breaking change:
Users might have accessed the public class `SmtInterpolEnvironment` for direct interaction with SMTInterpol.
We replace the class `org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolEnvironment`
with the class `de.uni_freiburg.informatik.ultimate.logic.Script`,
which provides a similar interface and also allows direct interaction with SMTInterpol.

### Updated solvers:
 - SMTInterpol 2.5-916-ga5843d8b
 - Boolector 3.2.2

## JavaSMT 3.10.1

This patch release brings several bugfixes for JavaSMT, for example,
in the bindings of Princess or for quantifier handling.
Additionally, we now provide Yices2 via Maven.

### Updated solvers:
 - SMTInterpol 2.5-842-gfcd46532

## JavaSMT 3.10.0

This release contains several improvement, some new features, several bugfixes and updated libraries.
A new method for loading native libraries is available for developers to use their own loading mechanism.
A new method `distinct` is available for Bitvector formulas.
The visitation of quantified formulas was improved.

### Updated solvers:
 - Princess 2021-08-12

## JavaSMT 3.9.0

This release contains a larger update of Princess and more JUnit tests.
The PrettyPrinter is switched from a boolean parameter to an options enum.
The example projects for Maven are updated with newer solver versions.

### Updated solvers:
 - Princess 2021-05-10 (improving Array and BV theory, and including a switch to an official Maven repository)

## JavaSMT 3.8.0

This release contains smaller bugfixes, some cleanup, and updated libraries.

### Updated solvers:
 - MathSAT5 5.6.6
 - Z3 4.8.10

## JavaSMT 3.7.0

This release contains the first official support for native SMT solvers on Windows.
We provide MathSAT5 and Z3 for Windows (64bit) as part of the Ivy build.
A user can of course exclude the native libraries from the dependencies,
if disk space is a critical point.

### Updated solvers:
 - MathSAT5 5.6.5 (inculding binary for Windows)
 - Z3 4.8.9 (including binaries for Windows and macOS)

## JavaSMT 3.6.1

### Updates solver versions:
 - Boolector 3.2.1-30-g95859db8
 - Princess 2.13 (2020-09-18)
 - SMTInterpol 2.5-732-gd208e931
 - Yices2 2.6.2-396-g194350c1
 - Z3 4.8.9

### Improvements:
 - Maven release is working again (available solvers: SMTInterpol and Princess)

## JavaSMT 3.6.0

### News on Solvers:
 - a new solver is available: Yices 2.6.2

### Licensing:
 - JavaSMT is now [REUSE](https://reuse.software/) compatible.

## JavaSMT 3.5.1

### Improvements and Fixes:
 - improve interpolation error detection for MathSAT5
 - fix simplification procedure for MathSAT5
 - improve interrupt detection for Z3
 - fix quantifier elimination for Z3

## JavaSMT 3.5.0

This release mostly contains updated solvers,
including the new version of Z3 without support for interpolation.
There were some internal fixes and improvements.

### Updates solver versions:
 - CVC4 prerelease-2020-06-13-g3a1bce1b8
 - Boolector 3.2.1-15-g59c9ade5
 - MathSAT5 5.6.3
 - OptiMathSAT 1.7.1
 - Princess 2.13
 - Z3 4.8.8 (info: interpolation no longer available!)

## JavaSMT 3.4.0

### Changes in the API:
 - With the update of SMTInterpol some partially visible classes were touched.

### Improvements and Fixes:
 - fix for visiting uninterpreted function with CVC4
 - New or updated solver versions:
    - SMTInterpol: 2.5-604-g71e72f93, including a small change in the API of SMTInterpol
 - Several updates for dependencies.

## JavaSMT 3.3.0

### Changes in the API:
 - FloatingPointManager supports more arithmetic methods, such as `min`, `max`, `abs`, `sqrt`.

### Improvements and Fixes:
 - More consistency checks on bitvector constants
 - The Maven release contains the bindings for Princess
 - New or updated solver versions:
    - Boolector 3.0.0-2019-11-11-g9d06cc0 was added (#174).
    - CVC4: 1.8-prerelease-2019-11-30-gae93e65
    - Princess: 2.12-2019-11-20
    - SMTInterpol: 2.5-533-ga4ba1513
    - other solvers were not updated since the last release

## JavaSMT 3.2.0

The biggest change is the integration of the CVC4 SMT solver (CVC4 1.8-prerelease).

## JavaSMT 3.1.0

This is mostly a cleanup release that contains several smaller changes and optimizations.

We included new solver versions:

- OptiMathSAT: 1.6.3
- SMTInterpol: 2.5-515-g2765bdd

## JavaSMT 3.0.0

### Changes in the API
 - New methods to cast different theories, e.g., BV to INT, REAL to INT, and vice versa.
 - More function declaration kinds, especially for FP theory.

### Improvements and Fixes
 - New solver versions:
    - MathSAT: 5.5.4 (Feb 2019)
    - SMTInterpol: 2.5-66-g453d36e
    - other solvers were not updated since the last release
 - Improve loading of Jar file for Z3 on Java 9 (and later).

## JavaSMT 2.0.0

### Changes in the API
 - New solver versions:
    - MathSAT: 5.5.3 (Nov 20 2018)
    - OptiMathSAT: 1.4.0.10
    - Princess: 2018-12-06-assertionless
    - SMTInterpol: 2.5-47-gc0546aa
    - Z3: 4.7.1.0
 - Methods for computing a model, unsat core and allsat are moved from
   `ProverEnvironment` upwards into `BasicProverEnvironment` and can now also
   be used in `InterpolatingProverEnvironment`
 - New methods to convert IEEE bitvectors to floats and vice versa.
 - Improved handling of exceptions
 - New method for evaluating formulas with an existing model
 - New utility methods for escaping and unescaping symbol names to avoid SMT keywords.

### Improvements and Fixes
 - Improve instantiation procedure of Z3 and Princess
 - Remove some non-determinism and prefer deterministic data structures
 - Fix model generation for SMTInterpol in case of multiple UF assignments

## JavaSMT 1.0.0

 - Floating point rounding mode can be now specified for all operations in
   `FloatingPointFormulaManager`.
   Additionally, default rounding mode can be set using an option
   `solver.floatingPointRoundingMode`.
 - Automatic boolean formula simplification for Z3.
 - New `utils` package, with optional utilities. Includes:
    - `UfElimination` class for performing Ackermannization and returning the
      metadata describing the fresh variables.
 - `modularCongruence` method was moved to `IntegerFormulaManager` and now
    throws an exception on non-positive input.
 - New package structure
    - Root package is `java_smt`
    - Solver bindings are in the package `java_smt/solvers`
    - User-facing API is in the package `java_smt/api`, apart from the entry
        point `SolverContextFactory`
 - Caching and statistics are moved to the `statistics` branch.

## JavaSMT 0.60-174-g7ab7771

 - New solver versions:
    - Z3: 4.4.1-1558-gf96cfea
    - MathSAT: 5.3.12
    - OptiMathSAT: 1.3.10
    - Princess: 2016-06-27-r2652
 - Better cancellation handling for Z3
 - Add `makeTrue()` and `makeFalse()` methods to `BooleanFormulaManager`
 - Added Ackermannization tactic.

## JavaSMT 0.60

 - Switched to Java8.
 - Change to the API for moving formulas between the contexts: the relevant
    method is now called `translateFrom`.
 - Incompatible public API change: migrated to Java `Optional`.
    Affects usages of `OptimizationProverEnvironment`.
 - `simplify` method can throw an `InterruptedException`.
 - Supported options are checked when creating a `ProverEnvironment`.
 - Our custom Z3 JNI is dropped, official JNI bindings from Z3 are used instead.
    `z3java` solver is dropped as well, since with the same JNI code other Java
    bindings only provide an extra wrapping layer.
 - Custom fork of Z3 is no longer required, using custom classloader to load
   Z3 Java bindings.
 - Adds `getModelAssignments` method to `ProverEnvironment`, which serializes
   the model to a list of assignments.
 - Switches to manual closing (try-with-resources) for `Model` objects.
 - Exposes API for calculating UNSAT core over assumptions.
    Assumptions feature is emulated in solvers which do not support it natively.
 - More descriptive name for prover options: `GENERATE_MODELS`,
    `GENERATE_UNSAT_CORE`, `GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS`.
 - Adds support for floating point theory in Z3.
 - Adds recursive transformation visitor for boolean formulas, which does not
    use recursion in its implementation
    (via `BooleanFormulaManager#transformRecursively`).
 - Many miscellaneous bugfixes.

## JavaSMT 0.51
