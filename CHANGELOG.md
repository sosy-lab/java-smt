# JavaSMT ChangeLog

## JavaSMT 2.0.0

### Changes in the API
 - New solver versions:
    - MathSAT: 5.5.0
    - OptiMathSAT: 1.4.0.10
    - Princess: 2017-12-06-assertionless
    - SMTInterpol: 2.1-335-g4c543a5
    - Z3: z3-4.6.0-9-g36204fa
 - Methods for computing a model, unsat core and allsat are moved from
   `ProverEnvironment` upwards into `BasicProverEnvironment` and can now also
   be used in `InterpolatingProverEnvironment`
 - New methods to convert IEEE bitvectors to floats and vice versa.
 - Improved handling of exceptions

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
