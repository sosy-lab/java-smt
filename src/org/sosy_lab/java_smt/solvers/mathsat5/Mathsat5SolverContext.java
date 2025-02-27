// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_opt_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_shared_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_shared_opt_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_version;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_option_checked;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.io.MoreFiles;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.TerminationCallback;
import org.sosy_lab.java_smt.test.ultimate.UltimateEliminatorWrapper;

public final class Mathsat5SolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.mathsat5")
  private static final class Mathsat5Settings {

    @Option(
        secure = true,
        description =
            "Further options that will be passed to Mathsat in addition to the default options. "
                + "Format is 'key1=value1,key2=value2'")
    private String furtherOptions = "";

    @Option(secure = true, description = "Load less stable optimizing version of mathsat5 solver.")
    boolean loadOptimathsat5 = false;

    private final @Nullable PathCounterTemplate logfile;

    private final ImmutableMap<String, String> furtherOptionsMap;

    private Mathsat5Settings(Configuration config, @Nullable PathCounterTemplate pLogfile)
        throws InvalidConfigurationException {
      config.inject(this);
      logfile = pLogfile;

      MapSplitter optionSplitter =
          Splitter.on(',')
              .trimResults()
              .omitEmptyStrings()
              .withKeyValueSeparator(Splitter.on('=').limit(2).trimResults());

      try {
        furtherOptionsMap = ImmutableMap.copyOf(optionSplitter.split(furtherOptions));
      } catch (IllegalArgumentException e) {
        throw new InvalidConfigurationException(
            "Invalid Mathsat option in \"" + furtherOptions + "\": " + e.getMessage(), e);
      }
    }
  }

  private static final boolean USE_SHARED_ENV = true;
  private static final boolean USE_GHOST_FILTER = true;

  private final LogManager logger;
  private final long mathsatConfig;
  private final Mathsat5Settings settings;
  private final long randomSeed;

  private final ShutdownNotifier shutdownNotifier;
  private final TerminationCallback terminationTest;
  private final Mathsat5FormulaCreator creator;
  private boolean closed = false;

  private static boolean loaded = false;

  @SuppressWarnings("checkstyle:parameternumber")
  private Mathsat5SolverContext(
      LogManager logger,
      long mathsatConfig,
      Mathsat5Settings settings,
      long randomSeed,
      final ShutdownNotifier shutdownNotifier,
      Mathsat5FormulaManager manager,
      Mathsat5FormulaCreator creator) {
    super(manager);

    logLicenseInfo(logger);
    this.logger = logger;
    this.mathsatConfig = mathsatConfig;
    this.settings = settings;
    this.randomSeed = randomSeed;
    this.shutdownNotifier = shutdownNotifier;
    this.creator = creator;

    terminationTest =
        () -> {
          shutdownNotifier.shutdownIfNecessary();
          return false;
        };
  }

  private static void logLicenseInfo(LogManager logger) {
    if (!loaded) { // Avoid logging twice.
      loaded = true;
      logger.log(
          Level.WARNING,
          "MathSAT5 is available for research and evaluation purposes only. It can not be used in"
              + " a commercial environment, particularly as part of a commercial product, without "
              + "written permission. MathSAT5 is provided as is, without any warranty. "
              + "Please write to mathsat@fbk.eu for additional questions regarding licensing "
              + "MathSAT5 or obtaining more up-to-date versions.");
    }
  }

  @SuppressWarnings("ParameterNumber")
  public static Mathsat5SolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogFile,
      long randomSeed,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {

    // Init Msat
    Mathsat5Settings settings = new Mathsat5Settings(config, solverLogFile);

    if (settings.loadOptimathsat5) {
      pLoader.accept("optimathsat5j");
    } else {
      loadLibrary(pLoader);
    }

    long msatConf = msat_create_config();
    msat_set_option_checked(msatConf, "theory.la.split_rat_eq", "false");
    msat_set_option_checked(msatConf, "random_seed", Long.toString(randomSeed));

    for (Map.Entry<String, String> option : settings.furtherOptionsMap.entrySet()) {
      try {
        msat_set_option_checked(msatConf, option.getKey(), option.getValue());
      } catch (IllegalArgumentException e) {
        throw new InvalidConfigurationException(e.getMessage(), e);
      }
    }
    final long msatEnv;
    if (settings.loadOptimathsat5) {
      msatEnv = msat_create_opt_env(msatConf);
    } else {
      msatEnv = msat_create_env(msatConf);
    }
    // Create Mathsat5FormulaCreator
    Mathsat5FormulaCreator creator = new Mathsat5FormulaCreator(msatEnv);

    // Create managers
    Mathsat5UFManager functionTheory = new Mathsat5UFManager(creator);
    Mathsat5BooleanFormulaManager booleanTheory = new Mathsat5BooleanFormulaManager(creator);
    Mathsat5IntegerFormulaManager integerTheory =
        new Mathsat5IntegerFormulaManager(creator, pNonLinearArithmetic);
    Mathsat5RationalFormulaManager rationalTheory =
        new Mathsat5RationalFormulaManager(creator, pNonLinearArithmetic);
    Mathsat5BitvectorFormulaManager bitvectorTheory =
        new Mathsat5BitvectorFormulaManager(creator, booleanTheory);
    Mathsat5FloatingPointFormulaManager floatingPointTheory =
        new Mathsat5FloatingPointFormulaManager(creator, pFloatingPointRoundingMode);
    Mathsat5ArrayFormulaManager arrayTheory = new Mathsat5ArrayFormulaManager(creator);
    Mathsat5EnumerationFormulaManager enumerationTheory =
        new Mathsat5EnumerationFormulaManager(creator);
    Mathsat5QuantifiedFormulaManager quantifiedTheory =
        new Mathsat5QuantifiedFormulaManager(creator, logger);
    Mathsat5FormulaManager manager =
        new Mathsat5FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            floatingPointTheory,
            quantifiedTheory,
            arrayTheory,
            enumerationTheory);
    quantifiedTheory.setFormulaManager(manager);
    return new Mathsat5SolverContext(
        logger, msatConf, settings, randomSeed, pShutdownNotifier, manager, creator);
  }

  @VisibleForTesting
  static void loadLibrary(Consumer<String> pLoader) {
    loadLibrariesWithFallback(
        pLoader, ImmutableList.of("mathsat5j"), ImmutableList.of("mpir", "mathsat", "mathsat5j"));
  }

  long createEnvironment(long cfg) {
    if (USE_GHOST_FILTER) {
      msat_set_option_checked(cfg, "dpll.ghost_filtering", "true");
    }

    msat_set_option_checked(cfg, "theory.la.split_rat_eq", "false");
    msat_set_option_checked(cfg, "random_seed", Long.toString(randomSeed));
    for (Map.Entry<String, String> option : settings.furtherOptionsMap.entrySet()) {
      msat_set_option_checked(cfg, option.getKey(), option.getValue());
    }

    if (settings.logfile != null) {
      Path filename = settings.logfile.getFreshPath();
      try {
        MoreFiles.createParentDirectories(filename);
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Cannot create directory for MathSAT logfile");
      }

      msat_set_option_checked(cfg, "debug.api_call_trace", "1");
      msat_set_option_checked(
          cfg, "debug.api_call_trace_filename", filename.toAbsolutePath().toString());
    }

    final long env;
    if (USE_SHARED_ENV) {
      if (settings.loadOptimathsat5) {
        env = msat_create_shared_opt_env(cfg, creator.getEnv());
      } else {
        env = msat_create_shared_env(cfg, creator.getEnv());
      }
    } else {
      if (settings.loadOptimathsat5) {
        env = msat_create_opt_env(cfg);
      } else {
        env = msat_create_env(cfg);
      }
    }

    return env;
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new Mathsat5TheoremProver(this, shutdownNotifier, creator, options);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new Mathsat5InterpolatingProver(this, shutdownNotifier, creator, options);
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new Mathsat5OptimizationProver(this, shutdownNotifier, creator, options);
  }

  @Override
  public String getVersion() {
    return msat_get_version();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.MATHSAT5;
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
      logger.log(Level.FINER, "Freeing Mathsat environment");
      msat_destroy_env(creator.getEnv());
      msat_destroy_config(mathsatConfig);
    }
  }

  /**
   * Get a termination callback for the current context. The callback can be registered upfront,
   * i.e., before calling a possibly expensive computation in the solver to allow a proper shutdown.
   */
  TerminationCallback getTerminationTest() {
    Preconditions.checkState(!closed, "solver context is already closed");
    return terminationTest;
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }
}
