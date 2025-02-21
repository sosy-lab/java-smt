package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.Set;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class SolverLessContext extends AbstractSolverContext {


  private SolverLessContext(SolverLessFormulaManager pManager) {
    super(pManager);
  }

  public static SolverLessContext create() {
    SolverLessFormulaCreator creator = new SolverLessFormulaCreator();
    SolverLessBooleanFormulaManager bmgr = new SolverLessBooleanFormulaManager(creator);
    SolverLessFormulaManager manager = new SolverLessFormulaManager(creator, bmgr);
    return new SolverLessContext(manager);
  }

  @Override
  public String getVersion() {
    return "SolverLess 1.0. Please note that this Solver has no SMT-Solving capabilities. It is "
        + "only used for SMTLIB2 generating.";
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.SOLVERLESS;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    throw new UnsupportedOperationException("SolverLess does not support ProverEnvironment.");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pOptions) {
    throw new UnsupportedOperationException("SolverLess does not support interpolation.");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pOptions) {
    throw new UnsupportedOperationException("SolverLess does not support optimization.");
  }

  @Override
  public void close() {
  }
}
