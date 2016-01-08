package org.sosy_lab.solver.api;

/**
 * Instances of this interface provide access to an SMT solver.
 * A single formula manager encapsulates a single solver context, and thus
 * should be used only from a single thread.
 *
 * <p>If you wish to use multiple contexts (even for the same solver),
 * create one SolverContext per each.
 * Formulas can be transferred between different contexts using
 * {@link FormulaManager#dumpFormula(BooleanFormula)} and
 * {@link FormulaManager#parse(String)} functions.
 */
public interface SolverContext extends AutoCloseable {

  /**
   * Get the formula manager, which is used for formula manipulation.
   */
  FormulaManager getFormulaManager();

  /**
   * Create a fresh new {@link ProverEnvironment} which encapsulates an assertion stack
   * and can be used to check formulas for unsatisfiability.
   * @param generateModels Whether the solver should generate models (i.e., satisfying assignments)
   *     for satisfiable formulas.
   * @param generateUnsatCore Whether the solver should generate an unsat core
   *     for unsatisfiable formulas.
   */
  ProverEnvironment newProverEnvironment(boolean generateModels, boolean generateUnsatCore);

  /**
   * Create a fresh new {@link InterpolatingProverEnvironment} which encapsulates an assertion stack
   * and allows to generate and retrieve interpolants for unsatisfiable formulas.
   * If the SMT solver is able to handle satisfiability tests with assumptions please consider
   * implementing the {@link InterpolatingProverEnvironmentWithAssumptions} interface, and return
   * an Object of this type here.
   */
  InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation();

  /**
   * Create a fresh new {@link OptEnvironment} which encapsulates an assertion stack
   * and allows to solve optimization queries.
   */
  OptEnvironment newOptEnvironment();

  /**
   * Get version information out of the solver.
   */
  String getVersion();

  /**
   * Close the solver context.
   * Necessary for solvers implemented in native code, frees the associated
   * memory.
   */
  void close();
}
