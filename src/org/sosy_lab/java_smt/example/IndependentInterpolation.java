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
import java.util.List;
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
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.independentInterpolation.IndependentInterpolatingEnvironment;

/**
 * Examples for using independent interpolation procedures.
 */
public class IndependentInterpolation {

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {

    // Set up a basic environment
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    // Choose solver
    Solvers solver = Solvers.Z3; // works for all solvers

    // Setup context
    try (SolverContext context =
             SolverContextFactory.createSolverContext(config, logger, notifier, solver);
         IndependentInterpolatingEnvironment<?> prover =
             (IndependentInterpolatingEnvironment<?>) context.newProverEnvironmentWithInterpolation()) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      // example
      prover.push();
      interpolateExample(prover, bmgr, imgr, logger);
      prover.pop();

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  private static <Formula> void interpolateExample(
      IndependentInterpolatingEnvironment<Formula> prover, BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr, LogManager logger) throws InterruptedException, SolverException {

    // Create some variables
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula two = imgr.makeNumber(2);

    // Create and assert some formulas
    Formula ip0 = prover.addConstraint(imgr.equal(x, zero));
    Formula ip1 = prover.addConstraint(bmgr.and(imgr.equal(y, imgr.add(x, two)),
        bmgr.not(imgr.equal(imgr.modulo(y, two), zero))));

    // Check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    List<BooleanFormula> itps;

    {
      itps = prover.getSeqInterpolants0(ImmutableList.of(ip0, ip1));
      logger.log(Level.INFO, "Example :: Interpolants for [{ip0},{ip1}] are:", itps);
    }
  }
}
