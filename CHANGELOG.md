# JavaSMT ChangeLog

## HEAD

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
