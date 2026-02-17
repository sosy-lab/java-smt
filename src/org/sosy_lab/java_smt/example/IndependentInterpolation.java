/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.example;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public final class IndependentInterpolation {

  private IndependentInterpolation() {
    // never called
  }

  private static final ProverOptions STRATEGY =
      ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS;

  public static void main(String[] args)
      throws InvalidConfigurationException, SolverException, InterruptedException {

    // set up a basic environment
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    // choose solver
    Solvers solver = Solvers.Z3;

    // setup context
    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        InterpolatingProverEnvironment<?> prover =
            context.newProverEnvironmentWithInterpolation(STRATEGY)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());
      logger.log(Level.INFO, "Interpolation strategy: " + STRATEGY);

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      // example
      prover.push();
      interpolateExample(prover, bmgr, imgr, logger);
      prover.pop();

      // another example
      prover.push();
      interpolateExample2(prover, bmgr, imgr, logger);
      prover.pop();

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  private static <T> void interpolateExample(
      InterpolatingProverEnvironment<T> prover,
      BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr,
      LogManager logger)
      throws InterruptedException, SolverException {

    // A: x = 1 && x = y
    // B: y = z && z = 2
    // -> y = 1, y != 2

    // create some variables
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula two = imgr.makeNumber(2);

    // create and assert some formulas
    // instead of 'named' formulas, we return a 'handle' (of generic type T)

    BooleanFormula formulaB = bmgr.and(imgr.equal(y, z), imgr.equal(z, two));
    BooleanFormula formulaA = bmgr.and(imgr.equal(x, one), imgr.equal(y, x));
    prover.addConstraint(formulaB);
    T ip1 = prover.addConstraint(formulaA);

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip1));
    logger.logf(
        Level.INFO,
            "Interpolation Result:%n"
                + "  Strategy: %s%n"
                + "  Formula A: %s%n"
                + "  Formula B: %s%n"
                + "  Interpolant: %s",
            STRATEGY,
            formulaA.toString().length() > 500 ? "Too large to display" : formulaA,
            formulaB.toString().length() > 500 ? "Too large to display" : formulaB,
            itp);
  }

  private static <T> void interpolateExample2(
      InterpolatingProverEnvironment<T> prover,
      BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr,
      LogManager logger)
      throws InterruptedException, SolverException {

    // A: x > 0 && y = x + 1
    // B: y < 0
    // -> y > 0

    // create some variables
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula zero = imgr.makeNumber(0);

    BooleanFormula formulaB = imgr.lessThan(y, zero);
    BooleanFormula formulaA = bmgr.and(imgr.greaterThan(x, zero), imgr.equal(y, imgr.add(x, one)));

    prover.addConstraint(formulaB);
    T ip1 = prover.addConstraint(formulaA);

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip1));
    logger.log(Level.INFO, "Interpolants are:", itp);
    logger.logf(
        Level.INFO,
            "Interpolation Result:%n"
                + "  Strategy: %s%n"
                + "  Formula A: %s%n"
                + "  Formula B: %s%n"
                + "  Interpolant: %s",
            STRATEGY,
            formulaA.toString().length() > 500 ? "Too large to display" : formulaA,
            formulaB.toString().length() > 500 ? "Too large to display" : formulaB,
            itp);
  }
}
