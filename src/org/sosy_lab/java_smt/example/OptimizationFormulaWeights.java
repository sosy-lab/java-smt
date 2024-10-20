// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import com.google.common.collect.ImmutableList;
import java.util.List;
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
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Example for optimizing the weight of some constraints. For a given set of formulas, the weight of
 * the satisfied formulas should be maximal and the weight of unsatisfied formulas should be
 * minimal.
 */
public final class OptimizationFormulaWeights {

  private OptimizationFormulaWeights() {
    // never called
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    Solvers solver = Solvers.Z3; // Z3 works for optimization

    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        OptimizationProverEnvironment prover =
            context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      optimizeWithWeights(prover, bmgr, imgr, logger);

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  /** add some constraints and then solve them with optimization according to weights. */
  private static void optimizeWithWeights(
      OptimizationProverEnvironment prover,
      BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr,
      LogManager logger)
      throws InterruptedException, SolverException {

    // create some symbols and formulas
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula four = imgr.makeNumber(4);
    IntegerFormula ten = imgr.makeNumber(10);

    IntegerFormula scoreBasic = imgr.makeNumber(0);
    IntegerFormula scoreLow = imgr.makeNumber(2);
    IntegerFormula scoreMedium = imgr.makeNumber(4);
    IntegerFormula scoreHigh = imgr.makeNumber(10);

    // add some very important constraints: x<10, y<10, z<10, 10=x+y+z
    prover.addConstraint(
        bmgr.and(
            imgr.lessOrEquals(x, ten), // very important -> direct constraint
            imgr.lessOrEquals(y, ten), // very important -> direct constraint
            imgr.lessOrEquals(z, ten), // very important -> direct constraint
            imgr.equal(ten, imgr.add(x, imgr.add(y, z)))));

    // generate weighted formulas: if a formula should be satisfied,
    // use higher weight for the positive instance than for its negated instance.
    List<IntegerFormula> weights =
        ImmutableList.of(
            bmgr.ifThenElse(imgr.lessOrEquals(x, zero), scoreHigh, scoreBasic), // important
            bmgr.ifThenElse(imgr.lessOrEquals(x, four), scoreHigh, scoreBasic), // important
            bmgr.ifThenElse(imgr.lessOrEquals(y, zero), scoreMedium, scoreBasic), // less important
            bmgr.ifThenElse(imgr.lessOrEquals(y, four), scoreMedium, scoreBasic), // less important
            bmgr.ifThenElse(imgr.lessOrEquals(z, zero), scoreLow, scoreBasic), // not important
            bmgr.ifThenElse(imgr.lessOrEquals(z, four), scoreHigh, scoreBasic) // important
            );

    // Maximize sum of weights
    int handle = prover.maximize(imgr.sum(weights));

    OptStatus response = prover.check();
    assert response == OptStatus.OPT;

    // for integer theory we get the optimal solution directly as model.
    // ideal solution: sum=32 with e.g. x=0,y=6,z=4  or  x=0,y=7,z=3  or  x=0,y=8,z=2 ...
    try (Model model = prover.getModel()) {
      logger.log(
          Level.INFO,
          "maximal sum ",
          prover.upper(handle, Rational.ZERO).orElseThrow(),
          "with model",
          model.asList());
    }
  }
}
