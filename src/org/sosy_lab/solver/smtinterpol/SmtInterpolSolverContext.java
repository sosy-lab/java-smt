package org.sosy_lab.solver.smtinterpol;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;

import javax.annotation.Nullable;

class SmtInterpolSolverContext extends AbstractSolverContext {

  private final SmtInterpolEnvironment environment;
  private final SmtInterpolFormulaManager manager;
  private final SmtInterpolFormulaCreator formulaCreator;

  private SmtInterpolSolverContext(
      Configuration configuration,
      LogManager logger,
      SmtInterpolFormulaCreator pFormulaCreator,
      SmtInterpolFormulaManager pManager)
      throws InvalidConfigurationException {
    super(configuration, logger, pManager);
    formulaCreator = pFormulaCreator;
    environment = pFormulaCreator.getEnv();
    manager = pManager;
  }

  public static SmtInterpolSolverContext create(
      Configuration config,
      LogManager logger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate smtLogfile,
      long randomSeed)
      throws InvalidConfigurationException {
    SmtInterpolEnvironment env =
        new SmtInterpolEnvironment(config, logger, pShutdownNotifier, smtLogfile, randomSeed);
    SmtInterpolFormulaCreator creator = new SmtInterpolFormulaCreator(env);
    SmtInterpolIntrospectionFormulaManager introspectionManager =
        new SmtInterpolIntrospectionFormulaManager(creator, env.getTheory());
    SmtInterpolFunctionFormulaManager functionTheory =
        new SmtInterpolFunctionFormulaManager(creator);
    SmtInterpolBooleanFormulaManager booleanTheory =
        new SmtInterpolBooleanFormulaManager(creator, env.getTheory(), introspectionManager);
    SmtInterpolIntegerFormulaManager integerTheory = new SmtInterpolIntegerFormulaManager(creator);
    SmtInterpolRationalFormulaManager rationalTheory =
        new SmtInterpolRationalFormulaManager(creator);
    SmtInterpolArrayFormulaManager arrayTheory = new SmtInterpolArrayFormulaManager(creator);
    SmtInterpolFormulaManager manager =
        new SmtInterpolFormulaManager(
            creator,
            introspectionManager,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            arrayTheory);
    return new SmtInterpolSolverContext(config, logger, creator, manager);
  }

  @Override
  public ProverEnvironment newProverEnvironment0(ProverOptions... options) {
    return environment.createProver(manager);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return environment.getInterpolator(manager);
  }

  @Override
  public OptEnvironment newOptEnvironment() {
    throw new UnsupportedOperationException("SMTInterpol does not support optimization");
  }

  @Override
  public FormulaManager getFormulaManager() {
    return manager;
  }

  @Override
  public String getVersion() {
    return environment.getVersion();
  }

  @Override
  public void close() {}
}
