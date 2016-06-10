package org.sosy_lab.solver.princess;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;
import org.sosy_lab.solver.reusableStack.ReusableStackInterpolatingProver;
import org.sosy_lab.solver.reusableStack.ReusableStackTheoremProver;

import java.util.Set;

import javax.annotation.Nullable;

public final class PrincessSolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.princess")
  static class PrincessOptions {
    @Option(
      secure = true,
      description =
          "The number of atoms a term has to have before"
              + " it gets abbreviated if there are more identical terms."
    )
    private int minAtomsForAbbreviation = 100;

    PrincessOptions(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }

    public int getMinAtomsForAbbreviation() {
      return minAtomsForAbbreviation;
    }
  }

  private final ShutdownNotifier shutdownNotifier;
  private final PrincessFormulaManager manager;
  private final PrincessFormulaCreator creator;

  private PrincessSolverContext(
      ShutdownNotifier shutdownNotifier,
      PrincessFormulaManager manager,
      PrincessFormulaCreator creator) {
    super(manager);
    this.shutdownNotifier = shutdownNotifier;
    this.manager = manager;
    this.creator = creator;
  }

  public static SolverContext create(
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pLogfileTemplate)
      throws InvalidConfigurationException {
    PrincessOptions options = new PrincessOptions(config);
    PrincessEnvironment env = new PrincessEnvironment(pLogfileTemplate, pShutdownNotifier, options);
    PrincessFormulaCreator creator =
        new PrincessFormulaCreator(env, PrincessTermType.Boolean, PrincessTermType.Integer);

    // Create managers
    PrincessUFManager functionTheory = new PrincessUFManager(creator);
    PrincessBooleanFormulaManager booleanTheory = new PrincessBooleanFormulaManager(creator);
    PrincessIntegerFormulaManager integerTheory = new PrincessIntegerFormulaManager(creator);
    PrincessArrayFormulaManager arrayTheory = new PrincessArrayFormulaManager(creator);
    PrincessQuantifiedFormulaManager quantifierTheory =
        new PrincessQuantifiedFormulaManager(creator);
    PrincessFormulaManager manager =
        new PrincessFormulaManager(
            creator, functionTheory, booleanTheory, integerTheory, arrayTheory, quantifierTheory);
    return new PrincessSolverContext(pShutdownNotifier, manager, creator);
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    if (options.contains(ProverOptions.GENERATE_UNSAT_CORE)
        || options.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      throw new UnsupportedOperationException("Princess does not support unsat core generation");
    }
    return new ReusableStackTheoremProver(
        new PrincessTheoremProver(manager, shutdownNotifier, creator));
  }

  @SuppressWarnings("resource")
  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return new ReusableStackInterpolatingProver<>(
        new PrincessInterpolatingProver(manager, creator));
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment() {
    throw new UnsupportedOperationException("Princess does not support optimization");
  }

  @Override
  public String getVersion() {
    return creator.getEnv().getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.PRINCESS;
  }

  @Override
  public void close() {}
}
