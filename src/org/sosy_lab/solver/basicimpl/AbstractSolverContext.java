package org.sosy_lab.solver.basicimpl;

import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

public abstract class AbstractSolverContext implements SolverContext {

  private final FormulaManager fmgr;

  protected AbstractSolverContext(FormulaManager fmgr) {
    this.fmgr = fmgr;
  }

  @Override
  public final FormulaManager getFormulaManager() {
    return fmgr;
  }

  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    Set<ProverOptions> opts = EnumSet.noneOf(ProverOptions.class);
    Collections.addAll(opts, options);
    return newProverEnvironment0(opts);
  }

  protected abstract ProverEnvironment newProverEnvironment0(Set<ProverOptions> options);

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

  protected abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0();
}
