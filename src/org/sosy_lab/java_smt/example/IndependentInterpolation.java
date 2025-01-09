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

/** Examples for using independent interpolation procedures. */
@SuppressWarnings("unused")
public class IndependentInterpolation {

  private IndependentInterpolation() {
    // never called
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {

    // set up a basic environment
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    // choose solver
    Solvers solver = Solvers.CVC5;

    // setup context
    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        InterpolatingProverEnvironment<?> prover =
            context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS,
                ProverOptions.GENERATE_MODEL_BASED_INTERPOLANTS)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      // example
      prover.push();
      interpolateExample(prover, bmgr, imgr, logger);
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

    // create some variables
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula two = imgr.makeNumber(2);

    // create and assert some formulas
    // instead of 'named' formulas, we return a 'handle' (of generic type T)

    // A := (x = 0)
    T ip0 = prover.push(imgr.equal(x, zero));
    // B := (y = x + 2) AND (y % 2 != 0)
    T ip1 =
        prover.push(
            bmgr.and(
                imgr.equal(y, imgr.add(x, two)), bmgr.not(imgr.equal(imgr.modulo(y, two), zero))));

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    assert ip0 != null;
    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip0));
    logger.log(Level.INFO, "Interpolants are:", itp);
  }
}
