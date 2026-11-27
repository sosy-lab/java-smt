package org.sosy_lab.java_smt.test;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.FallbackOptimizationProver;
import org.sosy_lab.java_smt.basicimpl.SolverVersionChecker;

import java.util.Optional;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class FallbackOptimizationTest extends SolverBasedTest0 {

    private SolverContext context;
    private IntegerFormulaManager imgr;
    private OptimizationProverEnvironment prover;

    @Before
    public void setUp() throws Exception {
        context = SolverContextFactory.createSolverContext(
            config, logger, shutdownNotifier, Solvers.PRINCESS);
        imgr = context.getFormulaManager().getIntegerFormulaManager();
        prover = new FallbackOptimizationProver(
            context, logger, context.getFormulaManager(), Set.of());
    }

    @Test
    public void testMaximize() throws SolverException, InterruptedException {
        // Create variables
        IntegerFormula x = imgr.makeVariable("x");
        IntegerFormula y = imgr.makeVariable("y");

        // Add constraints: x + y <= 10, x >= 0, y >= 0
        BooleanFormula constraint1 = imgr.lessOrEquals(
            imgr.add(x, y), imgr.makeNumber(10));
        BooleanFormula constraint2 = imgr.greaterOrEquals(x, imgr.makeNumber(0));
        BooleanFormula constraint3 = imgr.greaterOrEquals(y, imgr.makeNumber(0));

        prover.addConstraint(constraint1);
        prover.addConstraint(constraint2);
        prover.addConstraint(constraint3);

        // Maximize x + y
        int handle = prover.maximize(imgr.add(x, y));

        // Check result
        Optional<Rational> upper = prover.upper(handle, Rational.ofLong(1));
        assertTrue(upper.isPresent());
        assertEquals(Rational.ofLong(10), upper.get());
    }

    @Test
    public void testMinimize() throws SolverException, InterruptedException {
        // Create variables
        IntegerFormula x = imgr.makeVariable("x");
        IntegerFormula y = imgr.makeVariable("y");

        // Add constraints: x + y >= 5, x >= 0, y >= 0
        BooleanFormula constraint1 = imgr.greaterOrEquals(
            imgr.add(x, y), imgr.makeNumber(5));
        BooleanFormula constraint2 = imgr.greaterOrEquals(x, imgr.makeNumber(0));
        BooleanFormula constraint3 = imgr.greaterOrEquals(y, imgr.makeNumber(0));

        prover.addConstraint(constraint1);
        prover.addConstraint(constraint2);
        prover.addConstraint(constraint3);

        // Minimize x + y
        int handle = prover.minimize(imgr.add(x, y));

        // Check result
        Optional<Rational> lower = prover.lower(handle, Rational.ofLong(1));
        assertTrue(lower.isPresent());
        assertEquals(Rational.ofLong(5), lower.get());
    }
} 