package org.sosy_lab.java_smt.solvers.Solverless;

import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.Solverless.SolverLessFormulaCreator;
import org.sosy_lab.java_smt.solvers.Solverless.SolverLessFormulaManager;

public final class SolverLessContext extends AbstractSolverContext {

  private final SolverLessFormulaManager manager;

  private SolverLessContext(SolverLessFormulaManager pManager) {
    super(pManager);
    this.manager = pManager;
  }

  public static SolverLessContext create(
      Consumer<String> pLoader,
      ShutdownNotifier pShutdownNotifier) {
    pLoader.accept("SolverLess");
    SolverLessFormulaCreator creator = new SolverLessFormulaCreator();
    SolverLessFormulaManager manager = new SolverLessFormulaManager();
    return new SolverLessContext(manager);
  }

  @Override
  public String getVersion() {
    return "SolverLess 1.0";
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
