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
import org.sosy_lab.solver.AssignableTerm.Variable;
import org.sosy_lab.solver.FormulaManagerFactory.Solvers;
import org.sosy_lab.solver.Model;
import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;
import org.sosy_lab.solver.api.OptEnvironment;
import org.sosy_lab.solver.api.OptEnvironment.OptStatus;

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
    try (OptEnvironment prover = mgr.newOptEnvironment()) {
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
    try (OptEnvironment prover = mgr.newOptEnvironment()) {
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
    try (OptEnvironment prover = mgr.newOptEnvironment()) {

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
      BigInteger xValue = (BigInteger) model.get(new Variable("x", TermType.Integer));
      BigInteger objValue = (BigInteger) model.get(new Variable("obj", TermType.Integer));
      BigInteger yValue = (BigInteger) model.get(new Variable("y", TermType.Integer));

      assertThat(objValue).isEqualTo(BigInteger.valueOf(19));
      assertThat(xValue).isEqualTo(BigInteger.valueOf(10));
      assertThat(yValue).isEqualTo(BigInteger.valueOf(9));
    }
  }

  @Test
  public void testSwitchingObjectives() throws Exception {
    requireRationals();
    try (OptEnvironment prover = mgr.newOptEnvironment()) {
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
