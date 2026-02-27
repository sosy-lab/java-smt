/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.function.BiFunction;
import java.util.function.Function;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class MixedArithmeticsTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /** Require that the solver supports mixed integer-real arithmetics. */
  @Before
  public void requireMixedArithmetics() {
    requireIntegers();
    requireRationals();
    assume().that(solver).isNotEqualTo(Solvers.OPENSMT); // OpenSMT does not support mixed terms
  }

  /** Check if this unary operation returns the expected value. */
  private void testRationalOperation(
      Function<NumeralFormula, NumeralFormula> f, NumeralFormula arg, NumeralFormula expected)
      throws SolverException, InterruptedException {
    assertThatFormula(rmgr.equal(f.apply(arg), expected)).isTautological();
    assertThat(mgr.getFormulaType(f.apply(arg)).isRationalType()).isTrue();
  }

  /** Check if this binary operation returns the expected value. */
  private void testRationalOperation(
      BiFunction<NumeralFormula, NumeralFormula, NumeralFormula> f,
      NumeralFormula arg1,
      NumeralFormula arg2,
      NumeralFormula expected)
      throws SolverException, InterruptedException {
    assertThatFormula(rmgr.equal(f.apply(arg1, arg2), expected)).isTautological();
    assertThat(mgr.getFormulaType(f.apply(arg1, arg2)).isRationalType()).isTrue();
  }

  /** Same as unary testRationalOperation(), but we expect the result to be an integer term. */
  private void testIntegerOperation(
      Function<NumeralFormula, IntegerFormula> f, NumeralFormula arg, IntegerFormula expected)
      throws SolverException, InterruptedException {
    assertThatFormula(imgr.equal(f.apply(arg), expected)).isTautological();
    assertThat(mgr.getFormulaType(f.apply(arg)).isIntegerType()).isTrue();
  }

  @Test
  public void createIntegerNumberTest() throws SolverException, InterruptedException {
    IntegerFormula num1 = imgr.makeNumber(1.0);
    for (IntegerFormula num2 :
        ImmutableList.of(
            imgr.makeNumber(1.0),
            imgr.makeNumber("1"),
            imgr.makeNumber(1),
            imgr.makeNumber(BigInteger.ONE),
            imgr.makeNumber(BigDecimal.ONE),
            imgr.makeNumber(Rational.ONE))) {
      assertThatFormula(imgr.equal(num1, num2)).isTautological();
      assertThat(mgr.getFormulaType(num2).isIntegerType()).isTrue();
      assertThat(num2).isEqualTo(num1);
    }
  }

  @Test
  public void createRationalNumberTest() throws SolverException, InterruptedException {
    RationalFormula num1 = rmgr.makeNumber(1.0);
    for (RationalFormula num2 :
        ImmutableList.of(
            rmgr.makeNumber(1.0),
            rmgr.makeNumber("1"),
            rmgr.makeNumber(1),
            rmgr.makeNumber(BigInteger.ONE),
            rmgr.makeNumber(BigDecimal.ONE),
            rmgr.makeNumber(Rational.ONE))) {
      assertThatFormula(rmgr.equal(num1, num2)).isTautological();
      assertThat(mgr.getFormulaType(num2).isRationalType()).isTrue();
      assertThat(num2).isEqualTo(num1);
    }
  }

  @Test
  public void createRational2NumberTest() throws SolverException, InterruptedException {
    RationalFormula num1 = rmgr.makeNumber(1.5);
    for (RationalFormula num2 :
        ImmutableList.of(
            rmgr.makeNumber(1.5),
            rmgr.makeNumber("1.5"),
            rmgr.makeNumber(BigDecimal.valueOf(1.5)),
            rmgr.makeNumber(Rational.ofLongs(3, 2)))) {
      assertThatFormula(rmgr.equal(num1, num2)).isTautological();
      assertThat(mgr.getFormulaType(num2).isRationalType()).isTrue();
      // assertThat(num2).isEqualTo(num1); // some solvers do not normalize rational numbers
    }
  }

  @Test
  public void negateTest() throws SolverException, InterruptedException {
    testRationalOperation(rmgr::negate, imgr.makeNumber(1.5), rmgr.makeNumber(-1.0));
    testRationalOperation(rmgr::negate, rmgr.makeNumber(1.5), rmgr.makeNumber(-1.5));
  }

  @Test
  public void addTest() throws SolverException, InterruptedException {
    testRationalOperation(rmgr::add, imgr.makeNumber(2), imgr.makeNumber(1), rmgr.makeNumber(3.0));
    testRationalOperation(
        rmgr::add, imgr.makeNumber(2), rmgr.makeNumber(1.5), rmgr.makeNumber(3.5));
    testRationalOperation(
        rmgr::add, rmgr.makeNumber(1.5), imgr.makeNumber(2), rmgr.makeNumber(3.5));
    testRationalOperation(
        rmgr::add, rmgr.makeNumber(1.5), rmgr.makeNumber(2.5), rmgr.makeNumber(4.0));
  }

  @Test
  public void sumTest() throws SolverException, InterruptedException {
    assertThatFormula(
            rmgr.equal(
                rmgr.sum(ImmutableList.of(imgr.makeNumber(1), imgr.makeNumber(2))),
                rmgr.makeNumber(3)))
        .isTautological();
    assertThatFormula(
            rmgr.equal(
                rmgr.sum(ImmutableList.of(imgr.makeNumber(1), rmgr.makeNumber(1.5))),
                rmgr.makeNumber(2.5)))
        .isTautological();
    assertThatFormula(
            rmgr.equal(
                rmgr.sum(ImmutableList.of(rmgr.makeNumber(1.5), imgr.makeNumber(1))),
                rmgr.makeNumber(2.5)))
        .isTautological();
    assertThatFormula(
            rmgr.equal(
                rmgr.sum(ImmutableList.of(rmgr.makeNumber(0.5), rmgr.makeNumber(1.5))),
                rmgr.makeNumber(2)))
        .isTautological();
  }

  @Test
  public void subtractTest() throws SolverException, InterruptedException {
    testRationalOperation(
        rmgr::subtract, imgr.makeNumber(2), imgr.makeNumber(1), rmgr.makeNumber(1.0));
    testRationalOperation(
        rmgr::subtract, imgr.makeNumber(2), rmgr.makeNumber(1.5), rmgr.makeNumber(0.5));
    testRationalOperation(
        rmgr::subtract, rmgr.makeNumber(1.5), imgr.makeNumber(2), rmgr.makeNumber(-0.5));
    testRationalOperation(
        rmgr::subtract, rmgr.makeNumber(1.5), rmgr.makeNumber(0.5), rmgr.makeNumber(1.0));
  }

  @Test
  public void divideTest() throws SolverException, InterruptedException {
    testRationalOperation(
        rmgr::divide, imgr.makeNumber(1), imgr.makeNumber(2), rmgr.makeNumber(0.5));
    testRationalOperation(
        rmgr::divide, imgr.makeNumber(1), rmgr.makeNumber(2.0), rmgr.makeNumber(0.5));
    testRationalOperation(
        rmgr::divide, rmgr.makeNumber(1.0), imgr.makeNumber(2), rmgr.makeNumber(0.5));
    testRationalOperation(
        rmgr::divide, rmgr.makeNumber(1.0), rmgr.makeNumber(0.5), rmgr.makeNumber(2.0));
  }

  @Test
  public void multiplyTest() throws SolverException, InterruptedException {
    testRationalOperation(
        rmgr::multiply, imgr.makeNumber(2), imgr.makeNumber(3), rmgr.makeNumber(6.0));
    testRationalOperation(
        rmgr::multiply, imgr.makeNumber(2), rmgr.makeNumber(1.25), rmgr.makeNumber(2.5));
    testRationalOperation(
        rmgr::multiply, rmgr.makeNumber(1.25), imgr.makeNumber(2), rmgr.makeNumber(2.5));
    testRationalOperation(
        rmgr::multiply, rmgr.makeNumber(1.5), rmgr.makeNumber(2.5), rmgr.makeNumber(3.75));
  }

  @Test
  public void equalTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.equal(imgr.makeNumber(1.5), rmgr.makeNumber(1.0))).isTautological();
    assertThatFormula(rmgr.equal(rmgr.makeNumber(1.0), imgr.makeNumber(1.5))).isTautological();
  }

  @Test
  public void distinctTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.distinct(ImmutableList.of(imgr.makeNumber(1), imgr.makeNumber(2))))
        .isTautological();
    assertThatFormula(rmgr.distinct(ImmutableList.of(imgr.makeNumber(1), rmgr.makeNumber(1.5))))
        .isTautological();
    assertThatFormula(rmgr.distinct(ImmutableList.of(rmgr.makeNumber(1.5), imgr.makeNumber(2))))
        .isTautological();
    assertThatFormula(rmgr.distinct(ImmutableList.of(rmgr.makeNumber(1.5), imgr.makeNumber(1.0))))
        .isTautological();
  }

  @Test
  public void greaterThanTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(1.5), rmgr.makeNumber(0.5)))
        .isTautological();
    assertThatFormula(rmgr.greaterThan(rmgr.makeNumber(1.5), imgr.makeNumber(1.5)))
        .isTautological();

    assertThatFormula(rmgr.greaterThan(rmgr.makeNumber(1.5), imgr.makeNumber(1.5)))
        .isTautological();
    assertThatFormula(rmgr.greaterThan(rmgr.makeNumber(1.5), rmgr.makeNumber(1.5)))
        .isUnsatisfiable();
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(0.5), rmgr.makeNumber(0))).isUnsatisfiable();
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(0), rmgr.makeNumber(0))).isUnsatisfiable();
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(0), rmgr.makeNumber(0.5))).isUnsatisfiable();
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(1), rmgr.makeNumber(0.5))).isTautological();
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(1.5), rmgr.makeNumber(0.5)))
        .isTautological();
  }

  @Test
  public void greaterOrEqualTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.greaterOrEquals(imgr.makeNumber(1.5), rmgr.makeNumber(1.0)))
        .isTautological();
    assertThatFormula(rmgr.greaterOrEquals(rmgr.makeNumber(1.5), imgr.makeNumber(1.5)))
        .isTautological();
  }

  @Test
  public void lessThanTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.lessThan(imgr.makeNumber(1.5), rmgr.makeNumber(1.5))).isTautological();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(1.5), rmgr.makeNumber(1.5))).isUnsatisfiable();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(0), imgr.makeNumber(0.5))).isUnsatisfiable();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(0), imgr.makeNumber(0))).isUnsatisfiable();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(0.5), imgr.makeNumber(0))).isUnsatisfiable();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(0.5), imgr.makeNumber(1))).isTautological();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(0.5), imgr.makeNumber(1.5))).isTautological();
  }

  @Test
  public void lessOrEqualTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.lessOrEquals(imgr.makeNumber(1.5), rmgr.makeNumber(1.0)))
        .isTautological();
    assertThatFormula(rmgr.lessOrEquals(rmgr.makeNumber(1.5), imgr.makeNumber(2.0)))
        .isTautological();
  }

  @Test
  public void floorTest() throws SolverException, InterruptedException {
    requireRationalFloor();
    // FIXME Princess will loop forever. Report to the developers
    assume().that(solver).isNotEqualTo(Solvers.PRINCESS);
    testIntegerOperation(rmgr::floor, imgr.makeNumber(1.0), imgr.makeNumber(1.0));
    testIntegerOperation(rmgr::floor, rmgr.makeNumber(1.5), imgr.makeNumber(1.0));
  }

  @Test
  public void simplificationTest() throws InterruptedException {
    IntegerFormula sumInt = imgr.add(imgr.makeNumber(2), imgr.makeNumber(1));
    assertThat(mgr.getFormulaType(sumInt).isIntegerType()).isTrue();
    IntegerFormula simplifiedSumInt = mgr.simplify(sumInt);
    assertThat(mgr.getFormulaType(simplifiedSumInt).isIntegerType()).isTrue();

    RationalFormula sumRat = rmgr.add(rmgr.makeNumber(2.0), imgr.makeNumber(1.0));
    assertThat(mgr.getFormulaType(sumRat).isRationalType()).isTrue();
    RationalFormula simplifiedSumRat = mgr.simplify(sumRat);
    assertThat(mgr.getFormulaType(simplifiedSumRat).isRationalType()).isTrue();
  }
}
