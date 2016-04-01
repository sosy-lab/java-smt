package org.sosy_lab.solver.basicimpl;

import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;

public abstract class AbstractSolverContext implements SolverContext {

  private final FormulaManager fmgr;

  protected AbstractSolverContext(FormulaManager fmgr) {
    this.fmgr = fmgr;
  }

  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    return newProverEnvironment0(options);
  }

  public abstract ProverEnvironment newProverEnvironment0(ProverOptions... options);

  @SuppressWarnings("resource")
  @Override
  public final InterpolatingProverEnvironmentWithAssumptions<?>
      newProverEnvironmentWithInterpolation() {
    InterpolatingProverEnvironment<?> ipe = newProverEnvironmentWithInterpolation0();

    // In the case we do not already have a prover environment with assumptions
    // we add a wrapper to it
    InterpolatingProverEnvironmentWithAssumptions<?> out;
    if (!(ipe instanceof InterpolatingProverEnvironmentWithAssumptions)) {
      out = new InterpolatingProverWithAssumptionsWrapper<>(ipe, fmgr);
    } else {
      out = (InterpolatingProverEnvironmentWithAssumptions<?>) ipe;
    }
    return out;
  }

  public abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0();
}
