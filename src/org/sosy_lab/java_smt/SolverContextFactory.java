// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.LinkedHashSet;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.delegate.logging.LoggingSolverContext;
import org.sosy_lab.java_smt.delegate.statistics.StatisticsSolverContext;
import org.sosy_lab.java_smt.delegate.synchronize.SynchronizedSolverContext;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorSolverContext;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4SolverContext;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5SolverContext;
import org.sosy_lab.java_smt.solvers.princess.PrincessSolverContext;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolSolverContext;
import org.sosy_lab.java_smt.solvers.yices2.Yices2SolverContext;
import org.sosy_lab.java_smt.solvers.z3.Z3SolverContext;

/**
 * Factory class for loading and generating solver contexts. Generates a {@link SolverContext}
 * corresponding to the chosen solver.
 *
 * <p>Main entry point for JavaSMT.
 */
@Options(prefix = "solver")
public class SolverContextFactory {

  public enum Solvers {
    MATHSAT5,
    SMTINTERPOL,
    Z3,
    PRINCESS,
    BOOLECTOR,
    CVC4,
    YICES2
  }

  @Option(secure = true, description = "Export solver queries in SmtLib format into a file.")
  private boolean logAllQueries = false;

  @Option(secure = true, description = "Export solver queries in SmtLib format into a file.")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private @Nullable PathCounterTemplate logfile =
      PathCounterTemplate.ofFormatString("smtquery.%03d.smt2");

  @Option(
      secure = true,
      description = "If logging from the same application, avoid conflicting logfile names.")
  private boolean renameLogfileToAvoidConflicts = true;

  private static final Set<String> logfiles = new LinkedHashSet<>();

  @Option(secure = true, description = "Random seed for SMT solver.")
  private long randomSeed = 42;

  @Option(secure = true, description = "Which SMT solver to use.")
  private Solvers solver = Solvers.SMTINTERPOL;

  @Option(secure = true, description = "Log solver actions, this may be slow!")
  private boolean useLogger = false;

  @Option(
      secure = true,
      description = "Sequentialize all solver actions to allow concurrent access!")
  private boolean synchronize = false;

  @Option(
      secure = true,
      description = "Counts all operations and interactions towards the SMT solver.")
  private boolean collectStatistics = false;

  @Option(secure = true, description = "Default rounding mode for floating point operations.")
  private FloatingPointRoundingMode floatingPointRoundingMode =
      FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;

  @Option(
      secure = true,
      description =
          "Use non-linear arithmetic of the solver if supported and throw exception otherwise, "
              + "approximate non-linear arithmetic with UFs if unsupported, "
              + "or always approximate non-linear arithmetic. "
              + "This affects only the theories of integer and rational arithmetic.")
  private NonLinearArithmetic nonLinearArithmetic = NonLinearArithmetic.USE;

  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final Configuration config;

  public SolverContextFactory(
      Configuration pConfig, LogManager pLogger, ShutdownNotifier pShutdownNotifier)
      throws InvalidConfigurationException {
    pConfig.inject(this);
    logger = pLogger.withComponentName("JavaSMT");
    shutdownNotifier = checkNotNull(pShutdownNotifier);
    config = pConfig;

    if (!logAllQueries) {
      logfile = null;
    }

    if (logfile != null && renameLogfileToAvoidConflicts) {
      logfile = makeUniqueLogfile(logfile);
    }
  }

  /**
   * compute a new unused template. This method is helpful, if several instances of a solver are
   * used interleaved via JavaSMT and only one configuration is used.
   */
  private static synchronized PathCounterTemplate makeUniqueLogfile(PathCounterTemplate pLogfile) {
    final String original = pLogfile.getTemplate();
    final String extension = getFileExtension(original);
    final String basename = original.substring(0, original.length() - extension.length());
    String template = original;
    int counter = 0;
    while (logfiles.contains(template)) {
      counter++;
      template = basename + "." + counter + extension;
    }
    logfiles.add(template);
    return PathCounterTemplate.ofFormatString(template);
  }

  private static String getFileExtension(String path) {
    int lastIndexOf = path.lastIndexOf('.');
    return (lastIndexOf == -1) ? "" : path.substring(lastIndexOf);
  }

  /** Create new context with solver chosen according to the supplied configuration. */
  public SolverContext generateContext() throws InvalidConfigurationException {
    return generateContext(solver);
  }

  /** Create new context with solver name supplied. */
  @SuppressWarnings("resource") // returns unclosed context object
  public SolverContext generateContext(Solvers solverToCreate)
      throws InvalidConfigurationException {
    SolverContext context;
    try {
      context = generateContext0(solverToCreate);
    } catch (UnsatisfiedLinkError | NoClassDefFoundError e) {
      throw new InvalidConfigurationException(
          String.format(
              "The SMT solver %s is not available on this machine because of missing libraries "
                  + "(%s). "
                  + "You may experiment with SMTInterpol by setting solver.solver=SMTInterpol.",
              solverToCreate, e.getMessage()),
          e);
    }

    if (useLogger) {
      context = new LoggingSolverContext(logger, context);
    }
    if (synchronize) {
      context = new SynchronizedSolverContext(config, logger, shutdownNotifier, context);
    }
    if (collectStatistics) {
      // statistics need to be the most outer wrapping layer.
      context = new StatisticsSolverContext(context);
    }
    return context;
  }

  private SolverContext generateContext0(Solvers solverToCreate)
      throws InvalidConfigurationException {
    switch (solverToCreate) {
      case CVC4:
        return CVC4SolverContext.create(
            logger,
            shutdownNotifier,
            (int) randomSeed,
            nonLinearArithmetic,
            floatingPointRoundingMode);

      case SMTINTERPOL:
        return SmtInterpolSolverContext.create(
            config, logger, shutdownNotifier, logfile, randomSeed, nonLinearArithmetic);

      case MATHSAT5:
        return Mathsat5SolverContext.create(
            logger,
            config,
            shutdownNotifier,
            logfile,
            randomSeed,
            floatingPointRoundingMode,
            nonLinearArithmetic);

      case Z3:
        return Z3SolverContext.create(
            logger,
            config,
            shutdownNotifier,
            logfile,
            randomSeed,
            floatingPointRoundingMode,
            nonLinearArithmetic);

      case PRINCESS:
        return PrincessSolverContext.create(
            config, shutdownNotifier, logfile, (int) randomSeed, nonLinearArithmetic);

      case YICES2:
        return Yices2SolverContext.create(nonLinearArithmetic, shutdownNotifier);

      case BOOLECTOR:
        return BoolectorSolverContext.create(config, shutdownNotifier, logfile, (int) randomSeed);

      default:
        throw new AssertionError("no solver selected");
    }
  }

  /**
   * Shortcut for getting a {@link SolverContext}, the solver is selected using the configuration
   * {@code config}
   *
   * <p>See {@link #SolverContextFactory(Configuration, LogManager, ShutdownNotifier)} for
   * documentation of accepted parameters.
   */
  public static SolverContext createSolverContext(
      Configuration config, LogManager logger, ShutdownNotifier shutdownNotifier)
      throws InvalidConfigurationException {
    return new SolverContextFactory(config, logger, shutdownNotifier).generateContext();
  }

  /**
   * Shortcut for getting a {@link SolverContext}, the solver is selected using an argument.
   *
   * <p>See {@link #SolverContextFactory(Configuration, LogManager, ShutdownNotifier)} for
   * documentation of accepted parameters.
   */
  public static SolverContext createSolverContext(
      Configuration config, LogManager logger, ShutdownNotifier shutdownNotifier, Solvers solver)
      throws InvalidConfigurationException {
    return new SolverContextFactory(config, logger, shutdownNotifier).generateContext(solver);
  }

  /**
   * Minimalistic shortcut for creating a solver context. Empty default configuration, no logging,
   * and no shutdown notifier.
   *
   * @param solver Solver to initialize
   */
  public static SolverContext createSolverContext(Solvers solver)
      throws InvalidConfigurationException {
    return new SolverContextFactory(
            Configuration.defaultConfiguration(),
            LogManager.createNullLogManager(),
            ShutdownNotifier.createDummy())
        .generateContext(solver);
  }
}
