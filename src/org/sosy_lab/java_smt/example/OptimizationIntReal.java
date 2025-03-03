// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import java.util.Optional;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Example for optimizing 'x' with the constraint '0 &lt;= x &lt; 10'. We show the difference
 * between optimizing in integer and rational logic.
 */
public final class OptimizationIntReal {

  /** A correct value is determined in a region of size EPSILON around the real bound. */
  private static final Rational EPSILON = Rational.ofString("1/1000");

  private OptimizationIntReal() {
    // never called
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    Solvers solver = Solvers.Z3; // Z3 works for optimization

    optimizeWithIntegers(config, logger, notifier, solver);

    optimizeWithRationals(config, logger, notifier, solver);
  }

  /** Solve the problem with integer logic. */
  private static void optimizeWithIntegers(
      Configuration config, LogManager logger, ShutdownNotifier notifier, Solvers solver)
      throws InterruptedException, SolverException {
    // create solver context
    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        OptimizationProverEnvironment prover =
            context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager nmgr = context.getFormulaManager().getIntegerFormulaManager();
      IntegerFormula x = nmgr.makeVariable("x");

      // assert  0 <= x < 10
      prover.addConstraint(
          bmgr.and(
              nmgr.greaterOrEquals(x, nmgr.makeNumber(0)), nmgr.lessThan(x, nmgr.makeNumber(10))));

      logger.log(Level.INFO, "optimizing with integer logic");
      printUpperAndLowerBound(prover, x, logger);

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  /** Solve the problem with rational logic. */
  private static void optimizeWithRationals(
      Configuration config, LogManager logger, ShutdownNotifier notifier, Solvers solver)
      throws InterruptedException, SolverException {
    // create solver context
    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        OptimizationProverEnvironment prover =
            context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      RationalFormulaManager nmgr = context.getFormulaManager().getRationalFormulaManager();
      RationalFormula x = nmgr.makeVariable("x");

      prover.addConstraint(
          bmgr.and(
              nmgr.greaterOrEquals(x, nmgr.makeNumber(0)), nmgr.lessThan(x, nmgr.makeNumber(10))));

      logger.log(Level.INFO, "optimizing with rational logic");
      printUpperAndLowerBound(prover, x, logger);
    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  /** computes the lower and upper bound for the symbol 'x' and prints possible models. */
  private static void printUpperAndLowerBound(
      OptimizationProverEnvironment prover, NumeralFormula x, LogManager logger)
      throws InterruptedException, SolverException {

    prover.push();
    { // minimize x and get a lower bound of x: x >= 0
      // --> bound is 0
      int handleX = prover.minimize(x);
      OptStatus status = prover.check();
      assert status == OptStatus.OPT;
      Optional<Rational> lower = prover.lower(handleX, EPSILON);
      try (Model model = prover.getModel()) {
        logger.log(Level.INFO, "lower bound:", lower.orElseThrow(), "with model:", model.asList());
      }
    }
    prover.pop();

    prover.push();
    { // maximize x and get an upper bound of x: x < 10
      // --> bound is (10 - EPSILON) for rational symbols and 9 for integer symbols.
      int handleX = prover.maximize(x);
      OptStatus status = prover.check();
      assert status == OptStatus.OPT;
      Optional<Rational> upper = prover.upper(handleX, EPSILON);
      try (Model model = prover.getModel()) {
        logger.log(Level.INFO, "upper bound:", upper.orElseThrow(), "with model:", model.asList());
      }
    }
    prover.pop();
  }
}
