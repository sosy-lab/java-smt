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

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.regex.Pattern;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.ConsoleLogFormatter;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.SMTLibTokenizer;

/**
 * Main entry point for JavaSMT command-line interface. Executes SMT2 files using a selected solver
 * and reports the result (sat/unsat/unknown).
 *
 * <p>Contract for callers such as benchmarking frameworks: exactly one of <code>sat</code>, <code>
 * unsat</code>, or <code>unknown</code> is printed to stdout, all diagnostics and logging go to
 * stderr. The exit code is 0 for <code>sat</code> and <code>unsat</code>, and {@link
 * #ERROR_EXIT_CODE} for <code>unknown</code> and for all errors.
 */
public final class JavaSMTMain {

  /** Exit code for unknown results and for all errors. */
  public static final int ERROR_EXIT_CODE = 1;

  /**
   * Main method for running JavaSMT from command line.
   *
   * @param args Command-line arguments: [--solver SOLVER] [--logic LOGIC] file.smt2
   */
  public static void main(String[] args) {
    // JavaSMT uses American English for output, so make sure numbers are formatted appropriately.
    Locale.setDefault(Locale.US);

    // Ctrl+C or SIGTERM requests a shutdown from the solver, such that "unknown" is reported.
    ShutdownManager shutdownManager = ShutdownManager.create();
    ShutdownHook shutdownHook = new ShutdownHook(shutdownManager);
    Runtime.getRuntime().addShutdownHook(shutdownHook);

    int exitCode = run(args, System.out, System.err, shutdownManager.getNotifier());
    System.out.flush();
    System.err.flush();

    // The result is reported, the hook must not delay the exit anymore.
    shutdownHook.disableAndStop();
    System.exit(exitCode);
  }

  /**
   * Runs the command-line interface with the given arguments. This method has the same behavior as
   * {@link #main(String[])}, but writes to the given streams and returns the exit code instead of
   * terminating the JVM, such that it can be used from tests.
   *
   * @param args Command-line arguments: [--solver SOLVER] [--logic LOGIC] file.smt2
   * @param out output for the result, i.e., sat, unsat, unknown, or the help message
   * @param err output for diagnostics and logging
   * @param shutdownNotifier a shutdown request aborts the solver, and unknown is reported
   * @return exit code, 0 for sat and unsat, {@link #ERROR_EXIT_CODE} otherwise
   */
  public static int run(
      String[] args, Appendable out, Appendable err, ShutdownNotifier shutdownNotifier) {
    if (args.length == 0) {
      // be nice to user
      args = new String[] {"--help"};
    }

    final Map<String, String> cmdLineOptions;
    try {
      cmdLineOptions = CmdLineArguments.processArguments(args);
    } catch (InvalidCmdlineArgumentException e) {
      Output.error(err, "Could not process command line arguments: %s", e.getMessage());
      return ERROR_EXIT_CODE;
    }

    if (cmdLineOptions.remove(CmdLineArguments.HELP_OPTION) != null) {
      CmdLineArguments.printHelp(out);
      return 0;
    }

    final Configuration config;
    final MainOptions options;
    try {
      config = Configuration.builder().setOptions(cmdLineOptions).build();
      options = new MainOptions(config);
    } catch (InvalidConfigurationException e) {
      Output.error(err, "Invalid configuration: %s", e.getMessage());
      return ERROR_EXIT_CODE;
    }

    if (options.smt2File == null) {
      Output.error(err, "No SMT2 file given, see --help for usage.");
      return ERROR_EXIT_CODE;
    }

    LogManager logManager = createLogManager(err);

    if (cmdLineOptions.containsKey(CmdLineArguments.LOGIC_OPTION)
        && options.solver != Solvers.OPENSMT) {
      logManager.log(
          Level.WARNING,
          "Option --logic is only effective with OpenSMT solver, but solver is set to",
          options.solver + ". The logic setting will be ignored.");
    }

    final String input;
    try {
      input = Files.readString(Path.of(options.smt2File));
    } catch (IOException e) {
      Output.error(err, "Could not read SMT2 file: %s", e.getMessage());
      return ERROR_EXIT_CODE;
    }

    final Optional<String> scriptError;
    try {
      scriptError = checkScript(input);
    } catch (IllegalArgumentException e) {
      // The tokenizer rejects syntactically broken input, e.g., unbalanced parentheses.
      Output.error(err, "Could not parse SMT2 file: %s", describe(e));
      return ERROR_EXIT_CODE;
    }
    if (scriptError.isPresent()) {
      Output.error(err, "%s: %s", scriptError.orElseThrow(), options.smt2File);
      return ERROR_EXIT_CODE;
    }

    return solve(config, logManager, shutdownNotifier, options.solver, input, out, err);
  }

  private static int solve(
      Configuration config,
      LogManager logManager,
      ShutdownNotifier shutdownNotifier,
      Solvers solver,
      String input,
      Appendable out,
      Appendable err) {

    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logManager, shutdownNotifier, solver)) {

      // Parse before creating the prover: Princess does not know symbols that are declared after
      // the prover environment was created.
      final List<BooleanFormula> formulas;
      try {
        formulas = context.getFormulaManager().parseAll(input);
      } catch (IllegalArgumentException e) {
        // All parsers report input they cannot handle like this: syntax errors, undeclared
        // symbols, type errors, unsupported sorts or commands.
        Output.error(err, "Could not parse SMT2 file with %s: %s", solver, describe(e));
        return ERROR_EXIT_CODE;
      } catch (UnsupportedOperationException e) {
        // Solvers without a parser for SMT-LIB2, e.g., Yices2.
        Output.error(
            err,
            "Solver %s does not support parsing SMT-LIB2 input.%s",
            solver,
            e.getMessage() == null ? "" : " " + e.getMessage());
        return ERROR_EXIT_CODE;
      }
      // Any other exception is unexpected, e.g., a bug in a solver binding, and is intentionally
      // not caught, such that it terminates the program with a stack trace on stderr.

      boolean isUnsat;
      try (ProverEnvironment prover = context.newProverEnvironment()) {
        for (BooleanFormula formula : formulas) {
          prover.addConstraint(formula);
        }
        isUnsat = prover.isUnsat();
      }
      Output.println(out, isUnsat ? "unsat" : "sat");
      return 0;

    } catch (InvalidConfigurationException e) {
      Output.error(err, "Invalid configuration: %s", describe(e));
      return ERROR_EXIT_CODE;
    } catch (InterruptedException e) {
      // Thrown by the solver after a shutdown request, see ShutdownHook.
      String reason = shutdownNotifier.shouldShutdown() ? shutdownNotifier.getReason() : "";
      logManager.log(Level.WARNING, "SMT execution was interrupted.", reason);
      Output.println(out, "unknown");
      return ERROR_EXIT_CODE;
    } catch (SolverException e) {
      logManager.logUserException(Level.SEVERE, e, "Error executing SMT2 solver");
      Output.println(out, "unknown");
      return ERROR_EXIT_CODE;
    }
  }

  /** The message of an exception, or its class if it has no message. */
  private static String describe(Throwable e) {
    return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
  }

  /** Matches the commands <code>(check-sat)</code> and <code>(check-sat-assuming ..)</code>. */
  private static final Pattern CHECK_SAT_COMMAND = Pattern.compile("\\(\\s*check-sat[\\S\\s]*");

  /**
   * Checks the commands of the script for those that cannot be handled.
   *
   * <p>The parser silently ignores everything that is not a declaration, definition, or assertion,
   * so an empty or unparsable file would be reported as sat. Every benchmark that asks a question
   * contains (check-sat), so we require it.
   *
   * @return an error message if the script cannot be handled
   * @throws IllegalArgumentException if the tokenizer rejects the script, e.g., for unbalanced
   *     parentheses
   */
  private static Optional<String> checkScript(String input) {
    // TODO: parseAll does not track the assertion stack, i.e., (push ...) and (pop ...) are not
    // applied, and (reset) and (reset-assertions) are ignored. The assertions of a script using
    // these commands can therefore not be reconstructed, and such scripts are rejected here for
    // now.
    // The same holds for (exit) that is not the last command. To be supported once parseAll
    // handles the assertion stack and resets.
    boolean hasCheckSat = false;
    boolean afterExit = false;
    for (String token : SMTLibTokenizer.of(input)) {
      if (afterExit) {
        return Optional.of("Command (exit) is only allowed as the last command in the SMT2 file");
      }
      if (SMTLibTokenizer.isPopToken(token)
          || SMTLibTokenizer.isResetToken(token)
          || SMTLibTokenizer.isResetAssertionsToken(token)) {
        return Optional.of(
            "Command "
                + token
                + " is not supported, the assertion stack is not tracked when parsing SMT2 files");
      } else if (SMTLibTokenizer.isExitToken(token)) {
        afterExit = true;
      } else if (CHECK_SAT_COMMAND.matcher(token).matches()) {
        hasCheckSat = true;
      }
    }
    if (!hasCheckSat) {
      return Optional.of("SMT2 file contains no (check-sat) command");
    }
    return Optional.empty();
  }

  /** Creates a logger that writes messages of level INFO and above to the given output. */
  private static LogManager createLogManager(Appendable err) {
    Handler handler =
        new Handler() {
          @Override
          public void publish(LogRecord record) {
            if (isLoggable(record)) {
              try {
                err.append(getFormatter().format(record));
              } catch (IOException e) {
                throw new UncheckedIOException(e);
              }
            }
          }

          @Override
          public void flush() {}

          @Override
          public void close() {}
        };
    handler.setFormatter(ConsoleLogFormatter.withColorsIfPossible());
    handler.setLevel(Level.INFO);
    return BasicLogManager.createWithHandler(handler);
  }

  @Options
  private static final class MainOptions {

    private MainOptions(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }

    @Option(
        secure = true,
        name = CmdLineArguments.FILE_OPTION,
        description = "The SMT2 file to execute")
    private @Nullable String smt2File = null;

    @Option(
        secure = true,
        name = CmdLineArguments.SOLVER_OPTION,
        description = "The SMT solver to use")
    private Solvers solver = Solvers.SMTINTERPOL;
  }

  private JavaSMTMain() {}
}
