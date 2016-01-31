package org.sosy_lab.solver.test;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.ImmutableList;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.solver.basicimpl.Model;

import java.math.BigInteger;
import java.util.List;

@RunWith(Parameterized.class)
public class OptimizationTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    return super.createTestConfigBuilder().setOption("solver.mathsat5.loadOptimathsat5", "true");
  }

  @Before
  public void skipUnsupportedSolvers() throws Exception {
    requireOptimization();
  }

  @Test
  public void testUnbounded() throws Exception {
    requireRationals();
    assert rmgr != null;
    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x, obj;
      x = rmgr.makeVariable("x");
      obj = rmgr.makeVariable("obj");
      List<BooleanFormula> constraints =
          ImmutableList.of(rmgr.greaterOrEquals(x, rmgr.makeNumber("10")), rmgr.equal(x, obj));
      prover.addConstraint(bmgr.and(constraints));
      int handle = prover.maximize(obj);
      prover.check();
      assertThat(prover.upper(handle, Rational.ZERO)).isAbsent();
    }
  }

  @Test
  public void testUnfeasible() throws Exception {
    requireRationals();
    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x, y;
      x = rmgr.makeVariable("x");
      y = rmgr.makeVariable("y");
      List<BooleanFormula> constraints =
          ImmutableList.of(rmgr.lessThan(x, y), rmgr.greaterThan(x, y));
      prover.addConstraint(bmgr.and(constraints));
      prover.maximize(x);
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.UNSAT);
    }
  }

  @Test
  public void testOptimal() throws Exception {
    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {

      IntegerFormula x, y, obj;
      x = imgr.makeVariable("x");
      y = imgr.makeVariable("y");
      obj = imgr.makeVariable("obj");

      /*
       int x, y, obj
       x <= 10
       y <= 15
       obj = x + y
       x - y >= 1
      */
      List<BooleanFormula> constraints =
          ImmutableList.of(
              imgr.lessOrEquals(x, imgr.makeNumber(10)),
              imgr.lessOrEquals(y, imgr.makeNumber(15)),
              imgr.equal(obj, imgr.add(x, y)),
              imgr.greaterOrEquals(imgr.subtract(x, y), imgr.makeNumber(1)));

      prover.addConstraint(bmgr.and(constraints));
      int handle = prover.maximize(obj);

      // Maximize for x.
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);

      // Check the value.
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("19"));

      Model model = prover.getModel();
      BigInteger xValue = (BigInteger) model.evaluate(x).get();
      BigInteger objValue = (BigInteger) model.evaluate(obj).get();
      BigInteger yValue = (BigInteger) model.evaluate(y).get();

      assertThat(objValue).isEqualTo(BigInteger.valueOf(19));
      assertThat(xValue).isEqualTo(BigInteger.valueOf(10));
      assertThat(yValue).isEqualTo(BigInteger.valueOf(9));
    }
  }

  @Test
  public void testSwitchingObjectives() throws Exception {
    requireRationals();
    try (OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment()) {
      RationalFormula x, y, obj;
      x = rmgr.makeVariable("x");
      y = rmgr.makeVariable("y");
      obj = rmgr.makeVariable("obj");

      /*
       real x, y, obj
       x <= 10
       y <= 15
       obj = x + y
       x - y >= 1
      */
      List<BooleanFormula> constraints =
          ImmutableList.of(
              rmgr.lessOrEquals(x, rmgr.makeNumber(10)),
              rmgr.lessOrEquals(y, rmgr.makeNumber(15)),
              rmgr.equal(obj, rmgr.add(x, y)),
              rmgr.greaterOrEquals(rmgr.subtract(x, y), rmgr.makeNumber(1)));
      prover.addConstraint(bmgr.and(constraints));
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
}
