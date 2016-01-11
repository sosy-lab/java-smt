package org.sosy_lab.solver.basicimpl;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.logging.LoggingInterpolatingProverEnvironment;
import org.sosy_lab.solver.logging.LoggingProverEnvironment;

@Options(prefix = "solver")
public abstract class AbstractSolverContext implements SolverContext {

  @Option(secure = true, name = "useLogger", description = "Log solver actions, this may be slow!")
  private boolean useLogger = false;

  private final LogManager logger;
  private final FormulaManager fmgr;

  protected AbstractSolverContext(Configuration config, LogManager pLogger, FormulaManager fmgr)
      throws InvalidConfigurationException {
    logger = pLogger;
    this.fmgr = fmgr;
    config.inject(this, AbstractSolverContext.class);
  }

  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    ProverEnvironment pe = newProverEnvironment0(options);
    if (useLogger) {
      pe = new LoggingProverEnvironment(logger, pe);
    }
    return pe;
  }

  public abstract ProverEnvironment newProverEnvironment0(ProverOptions... options);

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
      out = (InterpolatingProverEnvironmentWithAssumptions) ipe;
    }

    if (useLogger) {
      out = new LoggingInterpolatingProverEnvironment<>(logger, out);
    }

    return out;
  }

  public abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0();
}
