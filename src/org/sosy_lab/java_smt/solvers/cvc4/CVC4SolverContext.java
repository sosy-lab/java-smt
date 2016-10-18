package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

import java.util.Set;

import javax.annotation.Nullable;

public final class CVC4SolverContext extends AbstractSolverContext {
  private final LogManager          logger;
  private final CVC4FormulaManager  manager;
  private final CVC4FormulaCreator  creator;

  private CVC4SolverContext(
      CVC4FormulaCreator creator,
      Configuration config,
      LogManager logger,
      CVC4FormulaManager manager)
      throws InvalidConfigurationException {
    super(manager);

    this.manager  = manager;
    this.creator  = creator;
    this.logger   = logger;
  }

  public static SolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogFile,
      int randomSeed)
      throws InvalidConfigurationException {

    // Init CVC4
    System.loadLibrary("cvc4jni");
    final CVC4Environment       env             = new CVC4Environment(randomSeed);
    CVC4FormulaCreator          creator         = new CVC4FormulaCreator(env);
    CVC4FunctionFormulaManager  functionTheory  = new CVC4FunctionFormulaManager(creator);
    CVC4BooleanFormulaManager   booleanTheory   = new CVC4BooleanFormulaManager(creator);
    CVC4IntegerFormulaManager   integerTheory   = new CVC4IntegerFormulaManager(creator);
    CVC4FormulaManager          manager         = new CVC4FormulaManager(creator, functionTheory, booleanTheory, integerTheory);

    return new CVC4SolverContext(creator, config, logger, manager);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    throw new UnsupportedOperationException("CVC4 does not support interpolation.");
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment() {
    throw new UnsupportedOperationException();
  }

  @Override
  public String getVersion() {
    return "CVC4 " + CVC4JNI.Configuration_getVersionString();
  }

  @Override
  public void close() {
    // TODO: closing context.
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC4;
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
