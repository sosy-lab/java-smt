package org.sosy_lab.solver.smtinterpol;

import static com.google.common.base.Preconditions.checkState;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;
import org.sosy_lab.solver.reusableStack.ReusableStackInterpolatingProver;
import org.sosy_lab.solver.reusableStack.ReusableStackTheoremProver;

import java.util.Set;

import javax.annotation.Nullable;

class SmtInterpolSolverContext extends AbstractSolverContext {

  private final SmtInterpolEnvironment environment;
  private final SmtInterpolFormulaManager manager;

  private SmtInterpolSolverContext(
      SmtInterpolFormulaCreator pFormulaCreator, SmtInterpolFormulaManager pManager) {
    super(pManager);
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
    SmtInterpolUFManager functionTheory = new SmtInterpolUFManager(creator);
    SmtInterpolBooleanFormulaManager booleanTheory =
        new SmtInterpolBooleanFormulaManager(creator, env.getTheory());
    SmtInterpolIntegerFormulaManager integerTheory = new SmtInterpolIntegerFormulaManager(creator);
    SmtInterpolRationalFormulaManager rationalTheory =
        new SmtInterpolRationalFormulaManager(creator);
    SmtInterpolArrayFormulaManager arrayTheory = new SmtInterpolArrayFormulaManager(creator);
    SmtInterpolFormulaManager manager =
        new SmtInterpolFormulaManager(
            creator, functionTheory, booleanTheory, integerTheory, rationalTheory, arrayTheory);
    return new SmtInterpolSolverContext(creator, manager);
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    checkState(
        environment.getStackDepth() == 0,
        "Not allowed to create a new prover environment while solver stack is still non-empty, "
            + "parallel stacks are not supported.");
    return new ReusableStackTheoremProver(
        new SmtInterpolTheoremProver(manager, manager.getFormulaCreator(), options));
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return new ReusableStackInterpolatingProver<>(environment.getInterpolator(manager));
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment() {
    throw new UnsupportedOperationException("SMTInterpol does not support optimization");
  }

  @Override
  public String getVersion() {
    return environment.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.SMTINTERPOL;
  }

  @Override
  public void close() {}
}
