# JavaSMT ChangeLog

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
