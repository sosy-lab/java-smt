package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_env;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_shared_env;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_version;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_option_checked;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_termination_test;

import com.google.common.base.Splitter;
import com.google.common.base.Splitter.MapSplitter;
import com.google.common.collect.ImmutableMap;

import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Files;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractSolverContext;
import org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.TerminationTest;

import java.io.IOException;
import java.util.Map.Entry;
import java.util.Set;
import java.util.logging.Level;

import javax.annotation.Nullable;

public final class Mathsat5SolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.mathsat5", deprecatedPrefix = "cpa.predicate.solver.mathsat5")
  private static class Mathsat5Settings {

    @Option(
      secure = true,
      description =
          "Further options that will be passed to Mathsat in addition to the default options. "
              + "Format is 'key1=value1,key2=value2'"
    )
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
  private final TerminationTest terminationTest;
  private final Mathsat5FormulaCreator creator;

  @SuppressWarnings("checkstyle:parameternumber")
  public Mathsat5SolverContext(
      LogManager logger,
      long mathsatConfig,
      Mathsat5Settings settings,
      long randomSeed,
      final ShutdownNotifier shutdownNotifier,
      Mathsat5FormulaManager manager,
      Mathsat5FormulaCreator creator) {
    super(manager);
    this.logger = logger;
    this.mathsatConfig = mathsatConfig;
    this.settings = settings;
    this.randomSeed = randomSeed;
    this.shutdownNotifier = shutdownNotifier;
    this.creator = creator;

    terminationTest =
        new TerminationTest() {
          @Override
          public boolean shouldTerminate() throws InterruptedException {
            shutdownNotifier.shutdownIfNecessary();
            return false;
          }
        };
  }

  public static Mathsat5SolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogFile,
      long randomSeed)
      throws InvalidConfigurationException {

    // Init Msat
    Mathsat5Settings settings = new Mathsat5Settings(config, solverLogFile);

    if (settings.loadOptimathsat5) {
      NativeLibraries.loadLibrary("optimathsat5j");
    } else {
      NativeLibraries.loadLibrary("mathsat5j");
    }

    long msatConf = msat_create_config();
    msat_set_option_checked(msatConf, "theory.la.split_rat_eq", "false");
    msat_set_option_checked(msatConf, "random_seed", Long.toString(randomSeed));

    for (Entry<String, String> option : settings.furtherOptionsMap.entrySet()) {
      try {
        msat_set_option_checked(msatConf, option.getKey(), option.getValue());
      } catch (IllegalArgumentException e) {
        throw new InvalidConfigurationException(e.getMessage(), e);
      }
    }

    final long msatEnv = msat_create_env(msatConf);

    // Create Mathsat5FormulaCreator
    Mathsat5FormulaCreator creator = new Mathsat5FormulaCreator(msatEnv);

    // Create managers
    Mathsat5UFManager functionTheory = new Mathsat5UFManager(creator);
    Mathsat5BooleanFormulaManager booleanTheory = new Mathsat5BooleanFormulaManager(creator);
    Mathsat5IntegerFormulaManager integerTheory = new Mathsat5IntegerFormulaManager(creator);
    Mathsat5RationalFormulaManager rationalTheory = new Mathsat5RationalFormulaManager(creator);
    Mathsat5BitvectorFormulaManager bitvectorTheory =
        Mathsat5BitvectorFormulaManager.create(creator);
    Mathsat5FloatingPointFormulaManager floatingPointTheory =
        new Mathsat5FloatingPointFormulaManager(creator, functionTheory);
    Mathsat5ArrayFormulaManager arrayTheory = new Mathsat5ArrayFormulaManager(creator);
    Mathsat5FormulaManager manager =
        new Mathsat5FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            floatingPointTheory,
            arrayTheory);
    return new Mathsat5SolverContext(
        logger, msatConf, settings, randomSeed, pShutdownNotifier, manager, creator);
  }

  long createEnvironment(long cfg) {
    if (USE_GHOST_FILTER) {
      msat_set_option_checked(cfg, "dpll.ghost_filtering", "true");
    }

    msat_set_option_checked(cfg, "theory.la.split_rat_eq", "false");
    msat_set_option_checked(cfg, "random_seed", Long.toString(randomSeed));

    for (Entry<String, String> option : settings.furtherOptionsMap.entrySet()) {
      msat_set_option_checked(cfg, option.getKey(), option.getValue());
    }

    if (settings.logfile != null) {
      Path filename = settings.logfile.getFreshPath();
      try {
        Files.createParentDirs(filename);
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Cannot create directory for MathSAT logfile");
      }

      msat_set_option_checked(cfg, "debug.api_call_trace", "1");
      msat_set_option_checked(
          cfg, "debug.api_call_trace_filename", filename.toAbsolutePath().toString());
    }

    final long env;
    if (USE_SHARED_ENV) {
      env = msat_create_shared_env(cfg, creator.getEnv());
    } else {
      env = msat_create_env(cfg);
    }

    return env;
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    return new Mathsat5TheoremProver(this, shutdownNotifier, creator, options);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return new Mathsat5InterpolatingProver(this, creator);
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment() {
    return new Mathsat5OptimizationProver(this, creator);
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
    logger.log(Level.FINER, "Freeing Mathsat environment");
    msat_destroy_env(creator.getEnv());
    msat_destroy_config(mathsatConfig);
  }

  long addTerminationTest(long env) {
    return msat_set_termination_test(env, terminationTest);
  }
}
