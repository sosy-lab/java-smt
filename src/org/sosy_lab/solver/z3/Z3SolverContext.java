package org.sosy_lab.solver.z3;

import com.microsoft.z3.Native;
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
import org.sosy_lab.common.io.MoreFiles;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.Set;
import java.util.logging.Level;

import javax.annotation.Nullable;

@Options(prefix = "solver.z3")
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
  private final long z3params;
  private final ShutdownNotifier shutdownNotifier;
  private final LogManager logger;
  private final Z3FormulaCreator creator;
  private final Z3FormulaManager manager;

  private static final String OPT_ENGINE_CONFIG_KEY = "optsmt_engine";
  private static final String OPT_PRIORITY_CONFIG_KEY = "priority";

  @Options(prefix = "solver.z3")
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
      long pZ3params,
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
              + "Please use the option solver.z3.log for a Z3-specific log instead.");
    }

    if (NativeLibraries.OS.guessOperatingSystem() == NativeLibraries.OS.WINDOWS) {
      // Z3 itself
      System.loadLibrary("libz3");
      System.loadLibrary("libz3java");
    }

    System.loadLibrary("z3");
    System.loadLibrary("z3java");

    if (extraOptions.log != null) {
      Path absolutePath = extraOptions.log.toAbsolutePath();
      try {
        // Z3 segfaults if it cannot write to the file, thus we write once first
        MoreFiles.writeFile(absolutePath, StandardCharsets.US_ASCII, "");
        Native.openLog(absolutePath.toString());
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Cannot write Z3 log file");
      }
    }

    long cfg = Native.mkConfig();
    Native.setParamValue(cfg, "MODEL", "true");

    if (extraOptions.requireProofs) {
      Native.setParamValue(cfg, "PROOF", "true");
    }
    Native.globalParamSet("smt.random_seed", String.valueOf(randomSeed));

    final long context = Native.mkContextRc(cfg);
    ShutdownNotifier.ShutdownRequestListener interruptListener =
        reason -> Native.interrupt(context);
    Native.delConfig(cfg);

    long boolSort = Native.mkBoolSort(context);
    Native.incRef(context, Native.sortToAst(context, boolSort));

    long integerSort = Native.mkIntSort(context);
    Native.incRef(context, Native.sortToAst(context, integerSort));
    long realSort = Native.mkRealSort(context);
    Native.incRef(context, Native.sortToAst(context, realSort));

    // The string representations of Z3s formulas should be in SMTLib2,
    // otherwise serialization wouldn't work.
    Native.setAstPrintMode(context, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT.toInt());

    long z3params = Native.mkParams(context);
    Native.paramsIncRef(context, z3params);
    Native.paramsSetUint(
        context, z3params, Native.mkStringSymbol(context, ":random-seed"), (int) randomSeed);

    Z3FormulaCreator creator =
        new Z3FormulaCreator(context, boolSort, integerSort, realSort, config, pShutdownNotifier);

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

    // Set the custom error handling
    // which will throw Z3Exception
    // instead of exit(1).
    Native.setInternalErrorHandler(context);

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
    Native.IntPtr major = new Native.IntPtr();
    Native.IntPtr minor = new Native.IntPtr();
    Native.IntPtr build = new Native.IntPtr();
    Native.IntPtr revision = new Native.IntPtr();
    Native.getVersion(major, minor, build, revision);
    return "Z3 " + major.value + "." + minor.value + "." + build.value + "." + revision.value;
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.Z3;
  }

  @Override
  public void close() {
    long context = creator.getEnv();
    Native.paramsDecRef(context, z3params);
    Native.closeLog();
    Native.delContext(context);
  }
}
