// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth8.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.Range;
import java.math.BigInteger;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class OptimizationTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Before
  public void checkNotSolverless() {
    assume().that(solverToUse()).isNotEqualTo(Solvers.SOLVERLESS);
  }

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    return super.createTestConfigBuilder().setOption("solver.mathsat5.loadOptimathsat5", "true");
  }

  @Before
  public void skipUnsupportedSolvers() {
    requireOptimization();
  }

  @Test
  public void testUnbounded() throws SolverException, InterruptedException {
    requireRationals();
    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x = rmgr.makeVariable("x");
      RationalFormula obj = rmgr.makeVariable("obj");
      prover.addConstraint(
          bmgr.and(rmgr.greaterOrEquals(x, rmgr.makeNumber("10")), rmgr.equal(x, obj)));
      int handle = prover.maximize(obj);
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);
      assertThat(prover.upper(handle, Rational.ZERO)).isEmpty();
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testUnfeasible() throws SolverException, InterruptedException {
    requireRationals();
    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x = rmgr.makeVariable("x");
      RationalFormula y = rmgr.makeVariable("y");
      prover.addConstraint(bmgr.and(rmgr.lessThan(x, y), rmgr.greaterThan(x, y)));
      prover.maximize(x);
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.UNSAT);
    }
  }

  @Test
  public void testOptimal() throws SolverException, InterruptedException {
    try (OptimizationProverEnvironment prover =
        context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula y = imgr.makeVariable("y");
      IntegerFormula obj = imgr.makeVariable("obj");

      /*
       int x, y, obj
       x <= 10
       y <= 15
       obj = x + y
       x - y >= 1
      */
      prover.addConstraint(
          bmgr.and(
              imgr.lessOrEquals(x, imgr.makeNumber(10)),
              imgr.lessOrEquals(y, imgr.makeNumber(15)),
              imgr.equal(obj, imgr.add(x, y)),
              imgr.greaterOrEquals(imgr.subtract(x, y), imgr.makeNumber(1))));
      int handle = prover.maximize(obj);

      // Maximize for x.
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);

      // Check the value.
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("19"));

      try (Model model = prover.getModel()) {
        BigInteger xValue = model.evaluate(x);
        BigInteger objValue = model.evaluate(obj);
        BigInteger yValue = model.evaluate(y);

        assertThat(objValue).isEqualTo(BigInteger.valueOf(19));
        assertThat(xValue).isEqualTo(BigInteger.valueOf(10));
        assertThat(yValue).isEqualTo(BigInteger.valueOf(9));
      }
    }
  }

  @Test(timeout = 20_000)
  public void testSwitchingObjectives() throws SolverException, InterruptedException {
    requireRationals();

    if (solverToUse() == Solvers.MATHSAT5) {
      // see https://github.com/sosy-lab/java-smt/issues/233
      assume()
          .withMessage("OptiMathSAT 1.7.2 has a bug with switching objectives")
          .that(context.getVersion())
          .doesNotContain("MathSAT5 version 1.7.2");
      assume()
          .withMessage("OptiMathSAT 1.7.3 has a bug with switching objectives")
          .that(context.getVersion())
          .doesNotContain("MathSAT5 version 1.7.3");
    }

    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x = rmgr.makeVariable("x");
      RationalFormula y = rmgr.makeVariable("y");
      RationalFormula obj = rmgr.makeVariable("obj");

      prover.push();

      /*
       real x, y, obj
       x <= 10
       y <= 15
       obj = x + y
       x - y >= 1
      */
      prover.addConstraint(
          bmgr.and(
              rmgr.lessOrEquals(x, rmgr.makeNumber(10)),
              rmgr.lessOrEquals(y, rmgr.makeNumber(15)),
              rmgr.equal(obj, rmgr.add(x, y)),
              rmgr.greaterOrEquals(rmgr.subtract(x, y), rmgr.makeNumber(1))));
      OptStatus response;

      prover.push();

      int handle = prover.maximize(obj);
      response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("19"));

      prover.pop();
      prover.push();

      handle = prover.maximize(x);
      response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("10"));

      prover.pop();
      prover.push();

      handle = prover.maximize(rmgr.makeVariable("y"));
      response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("9"));

      prover.pop();
    }
  }

  @Test
  public void testStrictConstraint() throws SolverException, InterruptedException {
    requireRationals();

    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x = rmgr.makeVariable("x");

      // assume (x < 1)
      prover.addConstraint(rmgr.lessThan(x, rmgr.makeNumber(1)));
      int handle = prover.maximize(x);
      assertThat(prover.check()).isEqualTo(OptStatus.OPT);

      // let's check how close we can get to value 1.
      for (long i : new long[] {1, 10, 100, 1000, 10000, 100000000L, 1000000000000L}) {
        long largeI = i * 1000000L; // increase precision
        Rational epsilon = Rational.ofLongs(1, largeI);
        Rational lowerBoundOfRange = Rational.ONE.minus(epsilon).minus(epsilon);
        Rational approximation = prover.upper(handle, epsilon).orElseThrow();
        assertThat(approximation).isIn(Range.closedOpen(lowerBoundOfRange, Rational.ONE));
      }

      // OptiMathSAT5 has at least an epsilon of 1/1000000. It does not allow larger values.
      assume()
          .withMessage("Solver %s does not support large epsilons", solverToUse())
          .that(solver)
          .isNotEqualTo(Solvers.MATHSAT5);

      for (long i : new long[] {1, 10, 100, 1000, 10000, 100000}) {
        Rational epsilon = Rational.ofLongs(1, i);
        Rational lowerBoundOfRange = Rational.ONE.minus(epsilon).minus(epsilon);
        Rational approximation = prover.upper(handle, epsilon).orElseThrow();
        assertThat(approximation).isIn(Range.closedOpen(lowerBoundOfRange, Rational.ONE));
      }

      // check strict value
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.of(1));
    }
  }
}
