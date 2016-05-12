package org.sosy_lab.solver.z3java;

import com.microsoft.z3.Context;
import com.microsoft.z3.Global;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Log;
import com.microsoft.z3.Params;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Version;
import com.microsoft.z3.enumerations.Z3_ast_print_mode;

import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.FileOption.Type;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import javax.annotation.Nullable;

@Options(prefix = "solver.z3java")
public final class Z3SolverContext extends AbstractSolverContext {

  /** Optimization settings */
  @Option(
    secure = true,
    description = "Engine to use for the optimization",
    values = {"basic", "farkas", "symba"}
  )
  String optimizationEngine = "basic";

  @Option(
    secure = true,
    description = "Ordering for objectives in the optimization" + " context",
    values = {"lex", "pareto", "box"}
  )
  String objectivePrioritizationMode = "box";

  private final ShutdownRequestListener interruptListener;
  private final Params z3params;
  private final ShutdownNotifier shutdownNotifier;
  private final LogManager logger;
  private final Z3FormulaCreator creator;
  private final Z3FormulaManager manager;

  private static final String OPT_ENGINE_CONFIG_KEY = "optsmt_engine";
  private static final String OPT_PRIORITY_CONFIG_KEY = "priority";

  @Options(prefix = "solver.z3java")
  private static class ExtraOptions {
    @Option(secure = true, description = "Require proofs from SMT solver")
    boolean requireProofs = true;

    @Option(
      secure = true,
      description =
          "Activate replayable logging in Z3."
              + " The log can be given as an input to the solver and replayed."
    )
    @FileOption(Type.OUTPUT_FILE)
    @Nullable
    Path log = null;
  }

  @SuppressWarnings("checkstyle:parameternumber")
  private Z3SolverContext(
      Z3FormulaCreator pFormulaCreator,
      Configuration config,
      Params pZ3params,
      ShutdownRequestListener pInterruptListener,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger,
      Z3FormulaManager pManager)
      throws InvalidConfigurationException {
    super(pManager);

    creator = pFormulaCreator;
    config.inject(this);
    z3params = pZ3params;
    interruptListener = pInterruptListener;
    pShutdownNotifier.register(interruptListener);
    shutdownNotifier = pShutdownNotifier;
    logger = pLogger;
    manager = pManager;
  }

  public static synchronized Z3SolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed)
      throws InvalidConfigurationException {
    ExtraOptions extraOptions = new ExtraOptions();
    config.inject(extraOptions);

    if (solverLogfile != null) {
      logger.log(
          Level.WARNING,
          "Z3 does not support dumping a log file in SMTLIB format. "
              + "Please use the option solver.z3java.log for a Z3-specific log instead.");
    }

    if (NativeLibraries.OS.guessOperatingSystem() == NativeLibraries.OS.WINDOWS) {
      // Z3 itself
      System.loadLibrary("libz3java");
    }

    System.loadLibrary("z3j");
    System.loadLibrary("z3java");

    if (extraOptions.log != null) {
      Path absolutePath = extraOptions.log.toAbsolutePath();
      Log.open(absolutePath.toString());
      // this is one static log for all contexts. Thus we might have interleaved logging.
      // TODO when should we close it?
    }

    Map<String, String> cfg = new HashMap<>();
    cfg.put("MODEL", "true");

    if (extraOptions.requireProofs) {
      cfg.put("PROOF", "true");
    }
    Global.setParameter("smt.random_seed", String.valueOf(randomSeed));

    // TODO add some other params, memory-limit?

    // TODO do we always need interpolation? how much overhead?
    // final Context context = new Context(cfg);
    final Context context = new InterpolationContext(cfg);

    ShutdownNotifier.ShutdownRequestListener interruptListener =
        new ShutdownNotifier.ShutdownRequestListener() {
          @Override
          public void shutdownRequested(String reason) {
            context.interrupt();
          }
        };

    Sort boolSort = context.getBoolSort();
    Sort integerSort = context.getIntSort();
    Sort realSort = context.getRealSort();

    // The string representations of Z3s formulas should be in SMTLib2,
    // otherwise serialization wouldn't work.
    context.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);

    Params z3params = context.mkParams();
    z3params.add(":random-seed", (int) randomSeed);

    Z3FormulaCreator creator = new Z3FormulaCreator(context, boolSort, integerSort, realSort);

    // Create managers
    Z3UFManager functionTheory = new Z3UFManager(creator);
    Z3BooleanFormulaManager booleanTheory = new Z3BooleanFormulaManager(creator);
    Z3IntegerFormulaManager integerTheory = new Z3IntegerFormulaManager(creator);
    Z3RationalFormulaManager rationalTheory = new Z3RationalFormulaManager(creator);
    Z3BitvectorFormulaManager bitvectorTheory = new Z3BitvectorFormulaManager(creator);
    Z3FloatingPointFormulaManager floatingPointTheory =
        new Z3FloatingPointFormulaManager(creator, functionTheory);
    Z3QuantifiedFormulaManager quantifierManager = new Z3QuantifiedFormulaManager(creator);
    Z3ArrayFormulaManager arrayManager = new Z3ArrayFormulaManager(creator);

    Z3FormulaManager manager =
        new Z3FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            floatingPointTheory,
            quantifierManager,
            arrayManager);
    return new Z3SolverContext(
        creator, config, z3params, interruptListener, pShutdownNotifier, logger, manager);
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    return new Z3TheoremProver(creator, manager, z3params, shutdownNotifier, options);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return new Z3InterpolatingProver(creator, z3params, shutdownNotifier);
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment() {
    Z3OptimizationProver out =
        new Z3OptimizationProver(getFormulaManager(), creator, shutdownNotifier, logger);
    out.setParam(OPT_ENGINE_CONFIG_KEY, this.optimizationEngine);
    out.setParam(OPT_PRIORITY_CONFIG_KEY, this.objectivePrioritizationMode);
    return out;
  }

  @Override
  public String getVersion() {
    return "Z3 " + Version.getString();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.Z3JAVA;
  }

  @Override
  public void close() {}
}
