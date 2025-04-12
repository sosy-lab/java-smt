// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.utils.PrettyPrinter.PrinterOption;
import org.sosy_lab.java_smt.utils.SolverUtils;

/** This program parses user-given formulas and prints them in a pretty format. */
@SuppressWarnings("unused")
public final class PrettyPrinter {

  /** Utility class without a public constructor. */
  private PrettyPrinter() {}

  /** We provide different types of output for the user. */
  private enum Type {
    /** dot-output with only boolean nodes. */
    DOT,
    /** dot-output with all operations/functions split into separate nodes. */
    DETAILED_DOT,
    /** text-output with only boolean formulas on separate lines. */
    TEXT,
    /** text-output with all operations/functions split to single lines. */
    DETAILED_TEXT
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException, IOException {

    if (args.length == 0) {
      help();
    }

    Solvers solver = Solvers.MATHSAT5;
    Type type = Type.TEXT;
    Path path = null;
    for (String arg : args) {
      if (arg.startsWith("-solver=")) {
        solver = Solvers.valueOf(arg.substring(8));
      } else if (arg.startsWith("-type=")) {
        type = Type.valueOf(arg.substring(6).toUpperCase(Locale.getDefault()));
      } else if (path == null) {
        path = Path.of(arg);
      } else {
        help();
      }
    }

    if (path == null) {
      help();
    }

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    // we need a solver that supports all theories, at least for parsing.
    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
      List<BooleanFormula> formulas = new ArrayList<>();

      // read all formulas from the file
      List<String> definitions = new ArrayList<>();
      for (String line : Files.readAllLines(path)) {
        // we assume a line-based content
        if (Iterables.any(
            ImmutableList.of(";", "(push ", "(pop ", "(reset", "(set-logic"), line::startsWith)) {
          continue;
        } else if (line.startsWith("(assert ")) {
          BooleanFormula bf =
              context.getFormulaManager().parse(Joiner.on("").join(definitions) + line);
          formulas.add(bf);
        } else {
          // it is a definition
          definitions.add(line);
        }
      }

      // classify the formulas
      org.sosy_lab.java_smt.utils.PrettyPrinter pp =
          SolverUtils.prettyPrinter(context.getFormulaManager());
      for (BooleanFormula formula : formulas) {
        System.out.println(formulaToString(formula, pp, type));
      }

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  private static String formulaToString(
      BooleanFormula formula, org.sosy_lab.java_smt.utils.PrettyPrinter pp, Type type) {
    switch (type) {
      case DETAILED_TEXT:
        return pp.formulaToString(formula);
      case DOT:
        return pp.formulaToDot(formula, PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS);
      case DETAILED_DOT:
        return pp.formulaToDot(formula);
      case TEXT:
      default:
        return pp.formulaToString(formula, PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS);
    }
  }

  private static void help() {
    throw new AssertionError("run $> TOOL [-solver=SOLVER] [-type=TYPE] PATH");
  }
}
