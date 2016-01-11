package org.sosy_lab.solver.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;

import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;

import java.util.EnumSet;

import javax.annotation.Nullable;

class CVC4SolverContext extends AbstractSolverContext {
  private final CVC4FormulaManager manager;

  private CVC4SolverContext(
      org.sosy_lab.common.configuration.Configuration config,
      LogManager logger,
      CVC4FormulaManager manager)
      throws InvalidConfigurationException {
    super(config, logger, manager);
    this.manager = manager;
  }

  public static SolverContext create(
      LogManager logger,
      org.sosy_lab.common.configuration.Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogFile,
      long randomSeed)
      throws InvalidConfigurationException {

    // Init CVC4
    NativeLibraries.loadLibrary("cvc4jni");

    edu.nyu.acsys.CVC4.Options cvc4options = new edu.nyu.acsys.CVC4.Options();
    // TODO set randomseed, furtherOptions

    final CVC4Environment env = new CVC4Environment(cvc4options);

    // Create CVC4FormulaCreator
    CVC4FormulaCreator creator = new CVC4FormulaCreator(env);

    // Create managers
    CVC4UnsafeFormulaManager ufmgr = new CVC4UnsafeFormulaManager(creator);
    CVC4FunctionFormulaManager ffmgr = new CVC4FunctionFormulaManager(creator);
    CVC4BooleanFormulaManager bfmgr = new CVC4BooleanFormulaManager(creator, ufmgr);
    CVC4IntegerFormulaManager ifmgr = new CVC4IntegerFormulaManager(creator);

    CVC4FormulaManager manager = new CVC4FormulaManager(creator, ufmgr, ffmgr, bfmgr, ifmgr);
    return new CVC4SolverContext(config, logger, manager);
  }

  @Override
  public FormulaManager getFormulaManager() {
    return manager;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(EnumSet<ProverOptions> options) {
    return new CVC4TheoremProver(manager);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    throw new UnsupportedOperationException("CVC4 does not support interpolation.");
  }

  @Override
  public OptEnvironment newOptEnvironment() {
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
}
