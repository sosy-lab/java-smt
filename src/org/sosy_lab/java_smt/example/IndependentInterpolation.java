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

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingEnvironment;

import java.util.logging.Level;

/**
 * Examples for using the solver independent interpolation procedures.
 */
public class IndependentInterpolation {

    public static void main(String... args)
            throws InvalidConfigurationException, SolverException, InterruptedException {
        // Set up a basic environment
        Configuration config = Configuration.defaultConfiguration();
        LogManager logger = BasicLogManager.create(config);
        ShutdownNotifier notifier = ShutdownNotifier.createDummy();

        // Choose solver
        SolverContextFactory.Solvers solver = SolverContextFactory.Solvers.SMTINTERPOL; // works for all interpolation strategies

        // Setup context
        try (SolverContext context =
                     SolverContextFactory.createSolverContext(config, logger, notifier, solver);
             IndependentInterpolatingEnvironment<?> prover =
                     context.newProverEnvironmentWithIndependentInterpolation()) {
            logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

            BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
            IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

            // example
            prover.push();
            interpolateExample(prover, bmgr, imgr);
            prover.pop();

        } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

            // on some machines we support only some solvers,
            // thus we can ignore these errors.
            logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

        } catch (UnsupportedOperationException e) {
            logger.logUserException(Level.INFO, e, e.getMessage());
        }
    }

    private static <Formula> void interpolateExample(
            IndependentInterpolatingEnvironment<Formula> prover, BooleanFormulaManager bmgr,
            IntegerFormulaManager imgr) throws InterruptedException {
        // Create some variables
        IntegerFormula a = imgr.makeVariable("a");
        IntegerFormula b = imgr.makeVariable("b");
        IntegerFormula x = imgr.makeVariable("x");

        // Create and assert some formulas
        Formula ip0 = prover.addConstraint(bmgr.and(imgr.lessThan(a, x), imgr.lessThan(x, b)));
        Formula ip1 = prover.addConstraint(imgr.greaterThan(a, b));

        // Perform model-based interpolation

    }

}
