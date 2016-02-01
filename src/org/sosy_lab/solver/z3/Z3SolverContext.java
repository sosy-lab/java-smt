package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3NativeApi.del_config;
import static org.sosy_lab.solver.z3.Z3NativeApi.del_context;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_version;
import static org.sosy_lab.solver.z3.Z3NativeApi.global_param_set;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.interrupt;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_bool_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_config;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_context_rc;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_int_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_params;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_real_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_string_symbol;
import static org.sosy_lab.solver.z3.Z3NativeApi.open_log;
import static org.sosy_lab.solver.z3.Z3NativeApi.params_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.params_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.params_set_uint;
import static org.sosy_lab.solver.z3.Z3NativeApi.setInternalErrorHandler;
import static org.sosy_lab.solver.z3.Z3NativeApi.set_ast_print_mode;
import static org.sosy_lab.solver.z3.Z3NativeApi.set_param_value;
import static org.sosy_lab.solver.z3.Z3NativeApi.sort_to_ast;

import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.FileOption.Type;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Files;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToInt;

import java.io.IOException;
import java.util.logging.Level;

import javax.annotation.Nullable;

@Options(prefix = "solver.z3", deprecatedPrefix = "cpa.predicate.solver.z3")
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
  private final Z3FormulaCreator formulaCreator;

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
    super(config, pLogger, pManager);

    formulaCreator = pFormulaCreator;
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
      NativeLibraries.loadLibrary("libz3");
    }

    NativeLibraries.loadLibrary("z3j");

    if (extraOptions.log != null) {
      Path absolutePath = extraOptions.log.toAbsolutePath();
      try {
        // Z3 segfaults if it cannot write to the file, thus we write once first
        Files.writeFile(absolutePath, "");

        open_log(absolutePath.toString());
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Cannot write Z3 log file");
      }
    }

    long cfg = mk_config();
    set_param_value(cfg, "MODEL", "true");

    if (extraOptions.requireProofs) {
      set_param_value(cfg, "PROOF", "true");
    }
    global_param_set("smt.random_seed", String.valueOf(randomSeed));

    // TODO add some other params, memory-limit?
    final long context = mk_context_rc(cfg);
    ShutdownNotifier.ShutdownRequestListener interruptListener =
        new ShutdownNotifier.ShutdownRequestListener() {
          @Override
          public void shutdownRequested(String reason) {
            interrupt(context);
          }
        };
    del_config(cfg);

    long boolSort = mk_bool_sort(context);
    inc_ref(context, sort_to_ast(context, boolSort));

    long integerSort = mk_int_sort(context);
    inc_ref(context, sort_to_ast(context, integerSort));
    long realSort = mk_real_sort(context);
    inc_ref(context, sort_to_ast(context, realSort));

    // The string representations of Z3s formulas should be in SMTLib2,
    // otherwise serialization wouldn't work.
    set_ast_print_mode(context, Z3NativeApiConstants.Z3_PRINT_SMTLIB2_COMPLIANT);

    long z3params = mk_params(context);
    params_inc_ref(context, z3params);
    params_set_uint(context, z3params, mk_string_symbol(context, ":random-seed"), (int) randomSeed);

    Z3FormulaCreator creator =
        new Z3FormulaCreator(context, boolSort, integerSort, realSort, config);

    // Create managers
    Z3FunctionFormulaManager functionTheory = new Z3FunctionFormulaManager(creator);
    Z3BooleanFormulaManager booleanTheory = new Z3BooleanFormulaManager(creator);
    Z3IntegerFormulaManager integerTheory = new Z3IntegerFormulaManager(creator);
    Z3RationalFormulaManager rationalTheory = new Z3RationalFormulaManager(creator);
    Z3BitvectorFormulaManager bitvectorTheory = new Z3BitvectorFormulaManager(creator);
    Z3QuantifiedFormulaManager quantifierManager = new Z3QuantifiedFormulaManager(creator);
    Z3ArrayFormulaManager arrayManager = new Z3ArrayFormulaManager(creator);

    // Set the custom error handling
    // which will throw java Exception
    // instead of exit(1).
    setInternalErrorHandler(context);

    Z3FormulaManager manager =
        new Z3FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            quantifierManager,
            arrayManager);
    return new Z3SolverContext(
        creator, config, z3params, interruptListener, pShutdownNotifier, logger, manager);
  }

  @Override
  public Z3FormulaManager getFormulaManager() {
    return manager;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(ProverOptions... options) {
    return new Z3TheoremProver(creator, manager, z3params, shutdownNotifier, options);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return new Z3InterpolatingProver(creator, z3params);
  }

  @Override
  public OptimizationProverEnvironment<?> newOptimizationProverEnvironment() {
    Z3OptimizationProver out =
        new Z3OptimizationProver(getFormulaManager(), creator, shutdownNotifier, logger);
    out.setParam(OPT_ENGINE_CONFIG_KEY, this.optimizationEngine);
    out.setParam(OPT_PRIORITY_CONFIG_KEY, this.objectivePrioritizationMode);
    return out;
  }

  @Override
  public String getVersion() {
    PointerToInt major = new PointerToInt();
    PointerToInt minor = new PointerToInt();
    PointerToInt build = new PointerToInt();
    PointerToInt revision = new PointerToInt();
    get_version(major, minor, build, revision);
    return "Z3 " + major.value + "." + minor.value + "." + build.value + "." + revision.value;
  }

  @Override
  public void close() {
    long context = formulaCreator.getEnv();
    params_dec_ref(context, z3params);
    del_context(context);
  }
}
