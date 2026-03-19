/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.cmdline;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableMap;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.annotations.SuppressForbidden;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Main entry point for JavaSMT command-line interface. Executes SMT2 files using a selected solver
 * and reports the result (sat/unsat/unknown).
 */
@SuppressForbidden("System.out in this class is ok")
public class JavaSMTMain {

  static final int ERROR_EXIT_CODE = 1;

  /**
   * Main method for running JavaSMT from command line.
   *
   * @param args Command-line arguments: [--solver SOLVER] [--logic LOGIC] file.smt2
   */
  @SuppressWarnings("resource") // We don't close LogManager
  public static void main(String[] args) {
    Locale.setDefault(Locale.US);

    if (args.length == 0) {
      args = new String[] {"--help"};
    }

    final Configuration config;
    final LogManager logManager;
    final MainOptions options;
    final Map<String, String> cmdLineOptions;
    try {
      cmdLineOptions = CmdLineArguments.processArguments(args);
      config = createConfiguration(cmdLineOptions);
      logManager = BasicLogManager.create(config);
      options = new MainOptions(config);

      String logic = cmdLineOptions.get("solver.opensmt.logic");
      String solver = cmdLineOptions.get("solver.solver");
      if (logic != null && (solver == null || !solver.equals("OPENSMT"))) {
        logManager.log(
            Level.WARNING,
            "Option --logic is only effective with OpenSMT solver, but solver is set to "
                + (solver != null ? solver : "default")
                + ". The logic setting will be ignored.");
      }
    } catch (InvalidCmdlineArgumentException e) {
      throw Output.fatalError("Could not process command line arguments: %s", e.getMessage());
    } catch (InvalidConfigurationException e) {
      throw Output.fatalError("Invalid configuration: %s", e.getMessage());
    }

    if (options.smt2File == null) {
      CmdLineArguments.printHelp(System.out);
      System.exit(0);
      return;
    }

    if (!Files.isReadable(Path.of(options.smt2File))) {
      throw Output.fatalError(
          "Please provide a valid, readable SMT2 file: %s", options.smt2File);
    }

    run(config, logManager, options);
  }

  private static final ImmutableMap<String, String> EXTERN_OPTION_DEFAULTS =
      ImmutableMap.of("log.level", Level.INFO.toString());

  @VisibleForTesting
  @Options
  static final class MainOptions {

    private MainOptions(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }

    @Option(secure = true, name = "smt2.file", description = "The SMT2 file to execute")
    private @Nullable String smt2File = null;

    @Option(secure = true, name = "solver.solver", description = "The SMT solver to use")
    private Solvers solver = Solvers.SMTINTERPOL;
  }

  /**
   * Creates a Configuration from command-line arguments.
   *
   * @param cmdLineOptions Processed command-line options map
   * @return Configuration object for solver context
   * @throws InvalidConfigurationException if configuration is invalid
   */
  @VisibleForTesting
  public static Configuration createConfiguration(Map<String, String> cmdLineOptions)
      throws InvalidConfigurationException {

    ConfigurationBuilder configBuilder = Configuration.builder();
    configBuilder.setOptions(EXTERN_OPTION_DEFAULTS);
    configBuilder.setOptions(cmdLineOptions);

    Configuration config = configBuilder.build();

    return config;
  }

  private static void run(Configuration config, LogManager logManager, MainOptions options) {

    String input;
    try {
      input = Files.readString(Path.of(options.smt2File));
    } catch (IOException e) {
      throw Output.fatalError("Could not read SMT2 file: %s", e.getMessage());
    }

    ShutdownManager shutdownManager = ShutdownManager.create();
    ShutdownNotifier notifier = shutdownManager.getNotifier();

    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logManager, notifier, options.solver);
        ProverEnvironment prover = context.newProverEnvironment()) {

      FormulaManager formulaManager = context.getFormulaManager();
      List<BooleanFormula> formulas = formulaManager.parseAll(input);
      for (BooleanFormula formula : formulas) {
        prover.addConstraint(formula);
      }

      boolean isUnsat = prover.isUnsat();
      System.out.println(isUnsat ? "unsat" : "sat");
      System.exit(0);

    } catch (InvalidConfigurationException e) {
      throw Output.fatalError("Invalid configuration: %s", e.getMessage());
    } catch (InterruptedException e) {
      logManager.log(Level.WARNING, "SMT execution was interrupted.");
      System.out.println("unknown");
      System.exit(ERROR_EXIT_CODE);
    } catch (SolverException e) {
      logManager.logUserException(Level.SEVERE, e, "Error executing SMT2 solver");
      System.out.println("unknown");
      System.exit(ERROR_EXIT_CODE);
    }
  }

  private JavaSMTMain() {}
}
