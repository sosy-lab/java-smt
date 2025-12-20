/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
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
            context.newProverEnvironmentWithInterpolation(
                ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

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
    prover.addConstraint(bmgr.and(imgr.equal(y, z), imgr.equal(z, two)));
    T ip1 = prover.addConstraint(bmgr.and(imgr.equal(x, one), imgr.equal(y, x)));

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip1));
    logger.log(Level.INFO, "Interpolants are:", itp);
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

    prover.addConstraint(imgr.lessThan(y, zero));
    T ip1 =
        prover.addConstraint(bmgr.and(imgr.greaterThan(x, zero), imgr.equal(y, imgr.add(x, one))));

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip1));
    logger.log(Level.INFO, "Interpolants are:", itp);
  }
}
