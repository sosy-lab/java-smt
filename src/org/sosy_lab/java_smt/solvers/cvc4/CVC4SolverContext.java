package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;

import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javax.annotation.Nullable;

public final class CVC4SolverContext extends AbstractSolverContext {
  private final CVC4FormulaManager manager;
  private final CVC4FormulaCreator creator;
  private static List<CVC4Environment> envs = new ArrayList<>();
  private static List<CVC4FormulaCreator> fCreators = new ArrayList<>();

  private static List<CVC4FormulaManager> fManagers = new ArrayList<>();
  private static List<CVC4FunctionFormulaManager> ffManagers = new ArrayList<>();
  private static List<CVC4BooleanFormulaManager> bfManagers = new ArrayList<>();
  private static List<CVC4IntegerFormulaManager> ifManagers = new ArrayList<>();

  private CVC4SolverContext(
      CVC4FormulaCreator creator,
      Configuration config,
      LogManager logger,
      CVC4FormulaManager manager)
      throws InvalidConfigurationException {
    super(manager);
    this.creator = creator;
    this.manager = manager;
  }

  public static SolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogFile,
      int randomSeed)
      throws InvalidConfigurationException {

    // Init CVC4
    NativeLibraries.loadLibrary("cvc4jni");
    final CVC4Environment env = new CVC4Environment(randomSeed);
    envs.add(env);

    // Create CVC4FormulaCreator
    CVC4FormulaCreator creator = new CVC4FormulaCreator(env);
    fCreators.add(creator);
    // Create managers
    CVC4FunctionFormulaManager ffmgr = new CVC4FunctionFormulaManager(creator);
    CVC4BooleanFormulaManager bfmgr = new CVC4BooleanFormulaManager(creator);
    CVC4IntegerFormulaManager ifmgr = new CVC4IntegerFormulaManager(creator);
    CVC4FormulaManager manager = new CVC4FormulaManager(creator, ffmgr, bfmgr, ifmgr);

//    ffManagers.add(ffmgr);
//    bfManagers.add(bfmgr);
//    ifManagers.add(ifmgr);
//    fManagers.add(manager);
    return new CVC4SolverContext(creator, config, logger, manager);
  }

  public FormulaManager getFormulaManager0() {
    return manager;
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
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new CVC4TheoremProver(creator, manager);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    // TODO Auto-generated method stub
    return false;
  }
}
