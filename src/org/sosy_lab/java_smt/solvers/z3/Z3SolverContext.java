// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Verify.verify;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_ast_print_mode;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.IO;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class Z3SolverContext extends AbstractSolverContext {

  private final ShutdownRequestListener interruptListener;
  private final ShutdownNotifier shutdownNotifier;
  private final LogManager logger;
  private final ExtraOptions extraOptions;
  private final Z3FormulaCreator creator;
  private final Z3FormulaManager manager;
  private final AtomicBoolean closed = new AtomicBoolean(false);
  private final Z3_ENGINE engine;
  private final Optional<String> logic;

  private final ImmutableMap<String, Object> solverOptionsFromConfig;

  // Options that require arguments of type double
  static final ImmutableSet<String> doubleOptions =
      ImmutableSet.of(
          "arith.epsilon",
          "dack.factor",
          "dack.gc_inv_decay",
          "qi.eager_threshold",
          "qi.lazy_threshold",
          "restart_factor",
          "spacer.dump_threshold");

  // Note: the options with : are named slightly differently when used normally
  private static final String RND_SEED_CONFIG_KEY = ":random-seed";
  private static final String UNSAT_CORE_CONFIG_KEY = ":unsat_core";
  private static final String MODEL_CONFIG_KEY = ":model";

  private static final String PROOF_GENERATION_CONFIG_KEY = "PROOF";
  private static final String SMT_RND_SEED_CONFIG_KEY = "smt.random_seed";
  private static final String OPT_ENGINE_CONFIG_KEY = "optsmt_engine";
  private static final String OPT_PRIORITY_CONFIG_KEY = "priority";

  static final String ENGINE_CONFIG_KEY = "engine";
  private static final String SOLVER_LOGIC_CONFIG_KEY = "logic";

  // All options need to be lowercase only!
  private static final ImmutableSet<String> OPTIONS_HANDLED_BY_DEDICATED_OPTIONS =
      ImmutableSet.of(
          "model",
          "unsat_core",
          "random_seed",
          SMT_RND_SEED_CONFIG_KEY, // NOT equal to "random_seed"!
          PROOF_GENERATION_CONFIG_KEY.toLowerCase(Locale.getDefault()),
          ENGINE_CONFIG_KEY,
          SOLVER_LOGIC_CONFIG_KEY,
          OPT_PRIORITY_CONFIG_KEY,
          OPT_ENGINE_CONFIG_KEY);

  enum Z3_ENGINE {
    DEFAULT {
      @Override
      public String toString() {
        return "auto-config";
      }
    },
    SPACER {
      @Override
      public String toString() {
        return "spacer";
      }
    },
    BMC {
      @Override
      public String toString() {
        return "bmc";
      }
    },
    DATALOG {
      @Override
      public String toString() {
        return "datalog";
      }
    }
  }

  @Options(prefix = "solver.z3")
  private static class ExtraOptions {

    @Option(secure = true, description = "Require proofs from SMT solver")
    boolean requireProofs = false;

    @Option(
        secure = true,
        description =
            "Activate replayable logging in Z3."
                + " The log can be given as an input to the solver and replayed.")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    @Nullable Path log = null;

    /** Optimization settings. */
    @Option(
        secure = true,
        description = "Engine to use for the optimization",
        values = {"basic", "farkas", "symba"})
    String optimizationEngine = "basic";

    // Uses option
    @Option(
        secure = true,
        description = "Ordering for objectives in the optimization context",
        values = {"lex", "pareto", "box"})
    String objectivePrioritizationMode = "box";

    @Option(
        secure = true,
        description =
            "Further options for Z3 in addition to the default options. "
                + "Format:  \"option.name=value\" with ’,’ to separate options. Spaces, as well "
                + "as capitalization in the options are allowed. "
                + "Option names and values can be found in the Z3 documentation online: "
                + "https://microsoft.github.io/z3guide/programming/Parameters/ "
                + "Example: \"spacer.order_children = 2, xform.inline_eager = FALSE, xform"
                + ".inline_linear=false,xform.slice=false,spacer.max_level=10\". Please use "
                + "the dedicated "
                + "configuration options, and not this option, for the following Z3 options: "
                + "logic, engine, optsmt_engine, priority, smt.random_seed, and random_seed. "
                + "Further, please do "
                + "not configure the following options, which are specified via JavaSMTs "
                + "ProverOptions: model, proof, unsat_core.")
    private String furtherOptions = "";

    @Option(
        secure = true,
        description =
            "Sets the engine to be used by this Z3 context, corresponding to Z3 option 'engine=.."
                + ".'. Default: auto-config",
        values = {"auto-config", "datalog", "bmc", "spacer"})
    private String engine = "auto-config";

    // Used when creating a solver. Note: Spacer requires the option 'spacer.logic=...'
    // if used, but that needs to be specified by the users!
    @Option(
        secure = true,
        description =
            "SMT-LIB logic to configure the SMT solvers (i.e. all Provers created from a"
                + " SolverContext with this option) with. Default: ALL. Note: this option does not"
                + " cover specialized logic selection, e.g. 'spacer.logic'! Please use"
                + " 'furtherOptions' for those.")
    private String logic = "ALL";

    private final @Nullable PathCounterTemplate logfile;

    private final int randomSeed;

    ExtraOptions(Configuration config, @Nullable PathCounterTemplate pLogfile, int pRandomSeed)
        throws InvalidConfigurationException {
      config.inject(this);

      randomSeed = pRandomSeed;
      logfile = pLogfile;
    }

    /**
     * Preprocesses the engine option string to {@link Z3_ENGINE}. Will also check for the correct
     * settings (as far as they are known) for non-default engines.
     */
    Z3_ENGINE getZ3Engine() {
      Z3_ENGINE z3Engine = Z3_ENGINE.DEFAULT;
      if (engine != null && !engine.strip().equalsIgnoreCase("AUTO-CONFIG")) {
        z3Engine = Z3_ENGINE.valueOf(engine.toUpperCase(Locale.getDefault()).strip());
      }
      // Spacer needs HORN logic
      // Note: seems like it does not need the option spacer.logic=HORN
      checkArgument(
          z3Engine != Z3_ENGINE.SPACER || getLogic().orElse("ALL").equalsIgnoreCase("HORN"),
          "Spacer requires HORN logic to be set");
      return z3Engine;
    }

    Optional<String> getLogic() {
      if (logic == null) {
        return Optional.empty();
      }
      // TODO: validate that this is a valid logic
      return Optional.of(logic.toUpperCase(Locale.getDefault()).strip());
    }

    String getFurtherOptions() {
      return furtherOptions;
    }
  }

  private Z3SolverContext(
      Z3FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger,
      Z3FormulaManager pManager,
      ExtraOptions pExtraOptions) {
    super(pManager);

    creator = pFormulaCreator;
    interruptListener = reason -> Native.interrupt(pFormulaCreator.getEnv());
    shutdownNotifier = pShutdownNotifier;
    pShutdownNotifier.register(interruptListener);
    logger = pLogger;
    manager = pManager;
    extraOptions = pExtraOptions;
    // Building the configuration based options right away allows us to throw immediately in case
    // of problems and not confuse the user
    solverOptionsFromConfig = buildSolverOptionsFromConfig(extraOptions);
    logic = extraOptions.getLogic();
    engine = extraOptions.getZ3Engine();
  }

  @SuppressWarnings("ParameterNumber")
  public static synchronized Z3SolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {
    ExtraOptions extraOptions = new ExtraOptions(config, solverLogfile, (int) randomSeed);

    // We need to load z3 in addition to z3java, because Z3's own class only loads the latter,
    // but it will fail to find the former if not loaded previously.
    // We load both libraries here to have all the loading in one place.
    loadLibrariesWithFallback(
        pLoader, ImmutableList.of("z3", "z3java"), ImmutableList.of("libz3", "libz3java"));

    // disable Z3's own loading mechanism, see com.microsoft.z3.Native
    System.setProperty("z3.skipLibraryLoad", "true");

    if (extraOptions.log != null) {
      Path absolutePath = extraOptions.log.toAbsolutePath();
      try {
        // Z3 segfaults if it cannot write to the file, thus we write once first
        IO.writeFile(absolutePath, StandardCharsets.US_ASCII, "");
        Native.openLog(absolutePath.toString());
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Cannot write Z3 log file");
      }
    }

    long cfg = Native.mkConfig();
    if (extraOptions.requireProofs) {
      Native.setParamValue(cfg, PROOF_GENERATION_CONFIG_KEY, "true");
    }
    Native.globalParamSet(SMT_RND_SEED_CONFIG_KEY, String.valueOf(randomSeed));
    Native.globalParamSet("model.compact", "false"); // This should be fine to set for users

    final long context = Native.mkContextRc(cfg);
    Native.delConfig(cfg);

    long boolSort = Native.mkBoolSort(context);
    Native.incRef(context, Native.sortToAst(context, boolSort));
    long integerSort = Native.mkIntSort(context);
    Native.incRef(context, Native.sortToAst(context, integerSort));
    long realSort = Native.mkRealSort(context);
    Native.incRef(context, Native.sortToAst(context, realSort));
    long stringSort = Native.mkStringSort(context);
    Native.incRef(context, Native.sortToAst(context, stringSort));
    long regexSort = Native.mkReSort(context, stringSort);
    Native.incRef(context, Native.sortToAst(context, regexSort));

    // The string representations of Z3s formulas should be in SMTLib2,
    // otherwise serialization wouldn't work.
    Native.setAstPrintMode(context, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT.toInt());

    Z3FormulaCreator creator =
        new Z3FormulaCreator(
            context,
            boolSort,
            integerSort,
            realSort,
            stringSort,
            regexSort,
            config,
            pShutdownNotifier);

    // Create managers
    Z3UFManager functionTheory = new Z3UFManager(creator);
    Z3BooleanFormulaManager booleanTheory = new Z3BooleanFormulaManager(creator);
    Z3IntegerFormulaManager integerTheory =
        new Z3IntegerFormulaManager(creator, pNonLinearArithmetic);
    Z3RationalFormulaManager rationalTheory =
        new Z3RationalFormulaManager(creator, pNonLinearArithmetic);
    Z3BitvectorFormulaManager bitvectorTheory =
        new Z3BitvectorFormulaManager(creator, booleanTheory);
    Z3FloatingPointFormulaManager floatingPointTheory =
        new Z3FloatingPointFormulaManager(creator, pFloatingPointRoundingMode);
    Z3QuantifiedFormulaManager quantifierManager = new Z3QuantifiedFormulaManager(creator);
    Z3ArrayFormulaManager arrayManager = new Z3ArrayFormulaManager(creator);
    Z3StringFormulaManager stringTheory = new Z3StringFormulaManager(creator);
    Z3EnumerationFormulaManager enumTheory = new Z3EnumerationFormulaManager(creator);

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
            arrayManager,
            stringTheory,
            enumTheory);
    return new Z3SolverContext(creator, pShutdownNotifier, logger, manager, extraOptions);
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    Preconditions.checkState(!closed.get(), "solver context is already closed");
    return new Z3TheoremProver(
        creator,
        manager,
        logic,
        engine,
        options,
        buildSolverOptions(options),
        extraOptions.logfile,
        shutdownNotifier);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    throw new UnsupportedOperationException("Z3 does not support interpolation");
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> options) {
    Preconditions.checkState(!closed.get(), "solver context is already closed");
    return new Z3OptimizationProver(
        creator,
        logger,
        manager,
        logic,
        engine,
        options,
        buildOptimizationSolverOptions(),
        extraOptions.logfile,
        shutdownNotifier);
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
    if (!closed.getAndSet(true)) {
      long context = creator.getEnv();
      creator.forceClose();
      shutdownNotifier.unregister(interruptListener);
      Native.closeLog();
      Native.delContext(context);
    }
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }

  private static ImmutableMap<String, Object> buildSolverOptionsFromConfig(
      ExtraOptions pExtraOptions) {
    ImmutableMap.Builder<String, Object> options = ImmutableMap.builder();
    Optional<String> maybeLogic = pExtraOptions.getLogic();
    if (!maybeLogic.orElse("ALL").equalsIgnoreCase("ALL")) {
      // Ignore default logic
      options.put(SOLVER_LOGIC_CONFIG_KEY, maybeLogic.orElseThrow());
    }
    return options.putAll(transformAdditionalOptions(pExtraOptions)).buildOrThrow();
  }

  private ImmutableMap<String, Object> buildSolverOptions(Set<ProverOptions> options) {
    return ImmutableMap.<String, Object>builder()
        .put(RND_SEED_CONFIG_KEY, extraOptions.randomSeed)
        .put(
            MODEL_CONFIG_KEY,
            options.contains(ProverOptions.GENERATE_MODELS)
                || options.contains(ProverOptions.GENERATE_ALL_SAT))
        .put(
            UNSAT_CORE_CONFIG_KEY,
            options.contains(ProverOptions.GENERATE_UNSAT_CORE)
                || options.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS))
        .putAll(solverOptionsFromConfig)
        .buildOrThrow();
  }

  private ImmutableMap<String, Object> buildOptimizationSolverOptions() {
    return ImmutableMap.<String, Object>builder()
        // .put(":random-seed", extraOptions.randomSeed) // not supported here
        .put(OPT_ENGINE_CONFIG_KEY, extraOptions.optimizationEngine)
        .put(OPT_PRIORITY_CONFIG_KEY, extraOptions.objectivePrioritizationMode)
        .putAll(solverOptionsFromConfig)
        .buildOrThrow();
  }

  /**
   * Resolves additional options set via the configuration (in the furtherOptions option). This must
   * be called after the context has been set up, as otherwise we don't get the solver info we need.
   */
  private static ImmutableMap<String, Object> transformAdditionalOptions(
      ExtraOptions pExtraOptions) {
    List<String> additionalOptions =
        Splitter.on(',')
            .splitToList(
                checkNotNull(pExtraOptions.getFurtherOptions())
                    .toLowerCase(Locale.getDefault())
                    .strip());
    if (additionalOptions.isEmpty()
        || (additionalOptions.size() == 1 && additionalOptions.get(0).isEmpty())) {
      // No extra options, ignore
      return ImmutableMap.of();
    }
    ImmutableMap.Builder<String, Object> optionsBuilder = ImmutableMap.builder();
    // Validate that options were not given twice!
    for (String option : additionalOptions) {
      checkArgument(option.contains("="));
      checkArgument(!option.contains(","));
      List<String> optionKeyAndValue = Splitter.on('=').splitToList(option);
      checkArgument(optionKeyAndValue.size() == 2);
      String key = optionKeyAndValue.get(0);
      String value = optionKeyAndValue.get(1);
      checkArgument(!key.isEmpty(), "Empty key for additional option with value: %s", value);
      checkArgument(!value.isEmpty(), "Empty value for additional option with key: %s", key);
      checkArgument(
          !OPTIONS_HANDLED_BY_DEDICATED_OPTIONS.contains(key),
          "Please handle option %s by its dedicated configuration option or ProverOption",
          key);

      // Transform value to its proper type
      optionsBuilder.put(key, transformZ3OptionValueToCorrectType(key, value));
    }
    return optionsBuilder.buildOrThrow();
  }

  private static Object transformZ3OptionValueToCorrectType(String optionName, String optionValue) {
    if (optionValue.equalsIgnoreCase("true") || optionValue.equalsIgnoreCase("false")) {
      return Boolean.valueOf(optionValue);
    } else if (doubleOptions.contains(optionName)) {
      // Numbers are either double or int
      return Double.valueOf(optionValue);
    }

    try {
      return Integer.valueOf(optionValue);
    } catch (NumberFormatException e) {
      return optionValue; // string or symbol (both as String)
    }
  }

  /**
   * Returns a {@link String} with all Z3 options (except tactic options as we can't use them).
   * Options are provided line by line (one option per line) with input types, information about the
   * option, and default values. This requires a fully formed Z3FormulaCreator to work!
   */
  String getAllZ3Options() {
    // Useful for retrieving all relevant Z3 options and their types
    // TODO: add a test that we know all 'double' option arguments.
    // TODO: add a public method that returns solver options?
    return getZ3SolverOptions() + getSimplifierOptions();
  }

  /**
   * Options string for all available options tied to solving (including fixed-point options like
   * BMC and Spacer options, and optimization options). The options are returned 1 per line, with
   * the pattern:
   *
   * <p>optionName{.detailedName} (type) infoText that may include brackets (default: defaultValue)
   *
   * <p>e.g.: arith.nl.horner_frequency (unsigned int) horner's call frequency (default: 4)
   */
  String getZ3SolverOptions() {
    long z3solver = Native.mkSolver(creator.getEnv());
    Native.solverIncRef(creator.getEnv(), z3solver);
    String options = Native.solverGetHelp(creator.getEnv(), z3solver);
    verify(options.endsWith("\n"));
    options += Native.fixedpointGetHelp(creator.getEnv(), z3solver);
    verify(options.endsWith("\n"));
    options += Native.optimizeGetHelp(creator.getEnv(), z3solver);
    checkArgument(
        Native.solverGetNumScopes(creator.getEnv(), z3solver) >= 0,
        "a negative number of scopes is not allowed");
    Native.solverReset(creator.getEnv(), z3solver); // just to be sure
    Native.solverDecRef(creator.getEnv(), z3solver);
    return options;
  }

  // TODO: do we allow tactic options currently?
  @SuppressWarnings("unused")
  String getTacticOptions() {
    long tactic = Native.mkTactic(creator.getEnv(), "simplify");
    Native.simplifierIncRef(creator.getEnv(), tactic);
    String options = Native.tacticGetHelp(creator.getEnv(), tactic);
    Native.simplifierDecRef(creator.getEnv(), tactic);
    return options;
  }

  String getSimplifierOptions() {
    long simplifier = Native.mkSimplifier(creator.getEnv(), "propagate-values");
    Native.simplifierIncRef(creator.getEnv(), simplifier);
    String options = Native.simplifierGetHelp(creator.getEnv(), simplifier);
    Native.simplifierDecRef(creator.getEnv(), simplifier);
    return options;
  }
}
