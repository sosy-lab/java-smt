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
import java.nio.file.InvalidPathException;
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
 * unsat</code>, or <code>unknown</code> is printed to stdout, or nothing in case of an error. All
 * diagnostics and logging go to stderr. The exit code is 0 for <code>sat</code> and <code>unsat
 * </code>, and {@link #ERROR_EXIT_CODE} for <code>unknown</code> and for all errors. If the JVM is
 * terminated by a signal, the exit code is the one of the JVM, e.g., 143 for SIGTERM.
 */
public final class JavaSMTMain {

  /** Exit code for unknown results and for all errors. */
  public static final int ERROR_EXIT_CODE = 1;

  /** The solver that is used if none is given on the command line. */
  static final Solvers DEFAULT_SOLVER = Solvers.SMTINTERPOL;

  private static final String COULD_NOT_PARSE_FILE = "Could not parse SMT2 file";
  private static final String INVALID_CONFIGURATION = "Invalid configuration: %s";

  /** Matches exactly the command <code>(check-sat)</code>. */
  private static final Pattern CHECK_SAT_COMMAND = Pattern.compile("\\(\\s*check-sat\\s*\\)");

  /** Matches every command starting with <code>check-sat</code>, e.g., check-sat-assuming. */
  private static final Pattern CHECK_SAT_LIKE_COMMAND =
      Pattern.compile("\\(\\s*check-sat[\\S\\s]*");

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
    // System.out and System.err do not throw on I/O errors but only record them internally,
    // so the result might not have been delivered even though nothing was reported.
    if (System.out.checkError() || System.err.checkError()) {
      exitCode = ERROR_EXIT_CODE;
    }

    // The result is reported, the hook must not delay the exit anymore.
    shutdownHook.disableAndStop();
    System.exit(exitCode);
  }

  /**
   * Runs the command-line interface with the given arguments. This method has the same behavior as
   * {@link #main(String[])}, but writes to the given streams and returns the exit code instead of
   * terminating the JVM, such that it can be used from tests.
   *
   * @param pArgs Command-line arguments: [--solver SOLVER] [--logic LOGIC] file.smt2
   * @param pOut output for the result, i.e., sat, unsat, unknown, or the help message
   * @param pErr output for diagnostics and logging
   * @param pShutdownNotifier a shutdown request aborts the solver, and unknown is reported
   * @return exit code, 0 for sat and unsat, {@link #ERROR_EXIT_CODE} otherwise
   */
  public static int run(
      String[] pArgs, Appendable pOut, Appendable pErr, ShutdownNotifier pShutdownNotifier) {
    final String[] args;
    if (pArgs.length == 0) {
      // be nice to user
      args = new String[] {CmdLineArguments.HELP_ARGUMENT};
    } else {
      args = pArgs;
    }

    final Map<String, String> cmdLineOptions;
    try {
      cmdLineOptions = CmdLineArguments.processArguments(args);
    } catch (InvalidCmdlineArgumentException e) {
      Output.error(pErr, "Could not process command line arguments: %s", e.getMessage());
      return ERROR_EXIT_CODE;
    }

    if (cmdLineOptions.remove(CmdLineArguments.HELP_OPTION) != null) {
      CmdLineArguments.printHelp(pOut);
      return 0;
    }

    final Configuration config;
    final MainOptions options;
    try {
      config = Configuration.builder().setOptions(cmdLineOptions).build();
      options = new MainOptions(config);
    } catch (InvalidConfigurationException e) {
      Output.error(pErr, INVALID_CONFIGURATION, describe(e));
      return ERROR_EXIT_CODE;
    }

    if (options.smt2File == null) {
      Output.error(pErr, "No SMT2 file given, see --help for usage.");
      return ERROR_EXIT_CODE;
    }

    LogManager logManager = createLogManager(pErr);

    // --logic sets the logic option of every solver that has one,
    // so either of them shows that it was given.
    if (cmdLineOptions.containsKey(CmdLineArguments.OPENSMT_LOGIC_OPTION)
        && !CmdLineArguments.SOLVERS_WITH_LOGIC_OPTION.contains(options.solver)) {
      logManager.logf(
          Level.WARNING,
          "Option --logic is only effective with the solvers OpenSMT and Z3, but solver is set"
              + " to %s. The logic setting will be ignored.",
          options.solver);
    }

    final String input;
    try {
      input = Files.readString(Path.of(options.smt2File));
    } catch (IOException | InvalidPathException e) {
      Output.error(pErr, "Could not read SMT2 file: %s", describe(e));
      return ERROR_EXIT_CODE;
    }

    final Optional<String> scriptError;
    try {
      scriptError = checkScript(input);
    } catch (IllegalArgumentException e) {
      // The tokenizer rejects syntactically broken input, e.g., unbalanced parentheses.
      Output.error(pErr, COULD_NOT_PARSE_FILE + ": %s", describe(e));
      return ERROR_EXIT_CODE;
    }
    if (scriptError.isPresent()) {
      Output.error(pErr, "%s: %s", scriptError.orElseThrow(), options.smt2File);
      return ERROR_EXIT_CODE;
    }

    return solve(config, logManager, pShutdownNotifier, options.solver, input, pOut, pErr);
  }

  /**
   * Parses the assertions of the script with the given solver and checks their satisfiability.
   *
   * @return exit code, 0 for sat and unsat, {@link #ERROR_EXIT_CODE} otherwise
   */
  private static int solve(
      Configuration pConfig,
      LogManager pLogManager,
      ShutdownNotifier pShutdownNotifier,
      Solvers pSolver,
      String pInput,
      Appendable pOut,
      Appendable pErr) {

    try (SolverContext context =
        SolverContextFactory.createSolverContext(
            pConfig, pLogManager, pShutdownNotifier, pSolver)) {

      // Parse before creating the prover: Princess does not know symbols that are declared after
      // the prover environment was created.
      final List<BooleanFormula> formulas;
      try {
        formulas = context.getFormulaManager().parseAll(pInput);
      } catch (IllegalArgumentException e) {
        // All parsers report input they cannot handle like this: syntax errors, undeclared
        // symbols, type errors, unsupported sorts or commands.
        Output.error(pErr, COULD_NOT_PARSE_FILE + " with %s: %s", pSolver, describe(e));
        return ERROR_EXIT_CODE;
      } catch (UnsupportedOperationException e) {
        // Solvers without a parser for SMT-LIB2, e.g., Yices2.
        final String details;
        if (e.getMessage() == null) {
          details = "";
        } else {
          details = " " + e.getMessage();
        }
        Output.error(
            pErr, "Solver %s does not support parsing SMT-LIB2 input.%s", pSolver, details);
        return ERROR_EXIT_CODE;
      }
      // Any other exception is unexpected, e.g., a bug in a solver binding, and is intentionally
      // not caught, such that it terminates the program with a stack trace on stderr.

      final SolverResult result;
      try (ProverEnvironment prover = context.newProverEnvironment()) {
        for (BooleanFormula formula : formulas) {
          prover.addConstraint(formula);
        }
        if (prover.isUnsat()) {
          result = SolverResult.UNSAT;
        } else {
          result = SolverResult.SAT;
        }
      }
      Output.println(pOut, result.toString());
      return 0;

    } catch (InvalidConfigurationException e) {
      Output.error(pErr, INVALID_CONFIGURATION, describe(e));
      return ERROR_EXIT_CODE;
    } catch (InterruptedException e) {
      // Thrown by the solver after a shutdown request, see ShutdownHook. The exception carries
      // the reason of the shutdown request.
      pLogManager.logUserException(Level.WARNING, e, "SMT execution was interrupted");
      Output.println(pOut, SolverResult.UNKNOWN.toString());
      return ERROR_EXIT_CODE;
    } catch (SolverException e) {
      pLogManager.logUserException(Level.SEVERE, e, "Error executing SMT2 solver");
      Output.println(pOut, SolverResult.UNKNOWN.toString());
      return ERROR_EXIT_CODE;
    }
  }

  /** The message of an exception, or its class if it has no message. */
  private static String describe(Throwable pException) {
    if (pException.getMessage() != null) {
      return pException.getMessage();
    } else {
      return pException.getClass().getSimpleName();
    }
  }

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
  private static Optional<String> checkScript(String pInput) {
    // TODO: parseAll does not track the assertion stack, i.e., (push ...) and (pop ...) are not
    // applied, and (reset) and (reset-assertions) are ignored. The assertions of a script using
    // these commands can therefore not be reconstructed, and such scripts are rejected here for
    // now. The same holds for (exit) that is not the last command.
    // Furthermore, each (check-sat) is a separate query over the assertions on the stack at that
    // point, but we perform a single check over all assertions of the script, so only one
    // (check-sat) is allowed, no assertion may follow it, and (check-sat-assuming ...) is not
    // supported.
    // To be supported once parseAll handles the assertion stack, resets, and check-sat commands.
    int checkSatCount = 0;
    boolean afterExit = false;
    for (String token : SMTLibTokenizer.of(pInput)) {
      if (afterExit) {
        return Optional.of("Command (exit) is only allowed as the last command in the SMT2 file");
      }
      if (!token.startsWith("(")) {
        // The parser silently ignores everything that is not a command.
        return Optional.of(String.format("Unexpected input '%s' in the SMT2 file", token));
      }
      if (SMTLibTokenizer.isForbiddenToken(token)) {
        // push, pop, reset-assertions, reset
        return Optional.of(
            String.format(
                "Command %s is not supported, the assertion stack is not tracked when parsing"
                    + " SMT2 files",
                token));
      } else if (SMTLibTokenizer.isExitToken(token)) {
        afterExit = true;
      } else if (CHECK_SAT_COMMAND.matcher(token).matches()) {
        checkSatCount++;
      } else if (CHECK_SAT_LIKE_COMMAND.matcher(token).matches()) {
        return Optional.of(
            String.format("Command %s is not supported, only (check-sat) is supported", token));
      } else if (SMTLibTokenizer.isAssertToken(token) && checkSatCount > 0) {
        return Optional.of(
            "Command (assert ...) after (check-sat) is not supported, all assertions have to"
                + " precede (check-sat)");
      }
    }
    if (checkSatCount == 0) {
      return Optional.of("SMT2 file contains no (check-sat) command");
    }
    if (checkSatCount > 1) {
      return Optional.of(
          String.format(
              "Only one (check-sat) command is supported, but the SMT2 file contains %d",
              checkSatCount));
    }
    return Optional.empty();
  }

  /** Creates a logger that writes messages of level INFO and above to the given output. */
  private static LogManager createLogManager(Appendable pErr) {
    Handler handler =
        new Handler() {
          @Override
          public void publish(LogRecord pRecord) {
            if (isLoggable(pRecord)) {
              try {
                pErr.append(getFormatter().format(pRecord));
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

    private MainOptions(Configuration pConfig) throws InvalidConfigurationException {
      pConfig.inject(this);
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
    private Solvers solver = DEFAULT_SOLVER;
  }

  private JavaSMTMain() {}
}
