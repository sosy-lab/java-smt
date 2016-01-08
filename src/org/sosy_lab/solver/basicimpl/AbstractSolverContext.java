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
  public final ProverEnvironment newProverEnvironment(
      boolean generateModels, boolean generateUnsatCore) {
    ProverEnvironment pe = newProverEnvironment0(generateModels, generateUnsatCore);
    if (useLogger) {
      pe = new LoggingProverEnvironment(logger, pe);
    }
    return pe;
  }

  public abstract ProverEnvironment newProverEnvironment0(
      boolean generateModels, boolean generateUnsatCore);

  @Override
  public final InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation() {
    InterpolatingProverEnvironment<?> ipe = newProverEnvironmentWithInterpolation0();

    // In the case we do not already have a prover environment with assumptions
    // we add a wrapper to it
    if (!(ipe instanceof InterpolatingProverEnvironmentWithAssumptions)) {
      ipe = new InterpolatingProverWithAssumptionsWrapper<>(ipe, fmgr);
    }

    if (useLogger) {
      ipe =
          new LoggingInterpolatingProverEnvironment<>(
              logger, (InterpolatingProverEnvironmentWithAssumptions<?>) ipe);
    }

    return ipe;
  }

  public abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0();
}
