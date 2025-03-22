/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import java.util.function.BiFunction;
import java.util.function.Function;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class MixedArithmeticsTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /** Require that the solver supports mixed integer-real arithmetics */
  @Before
  public void requireMixedArithmetics() {
    requireIntegers();
    requireRationals();
    assume().that(solver).isNotEqualTo(Solvers.OPENSMT); // OpenSMT does not support mixed terms
  }

  /** Check if this unary operation returns the expected value. */
  private void testOperation(
      Function<NumeralFormula, NumeralFormula> f, NumeralFormula arg, NumeralFormula expected)
      throws SolverException, InterruptedException {
    assertThatFormula(rmgr.equal(f.apply(arg), expected)).isSatisfiable();
    assertThat(mgr.getFormulaType(f.apply(arg)).isRationalType()).isTrue();
  }

  /** Check if this binary operation returns the expected value. */
  private void testOperation(
      BiFunction<NumeralFormula, NumeralFormula, NumeralFormula> f,
      NumeralFormula arg1,
      NumeralFormula arg2,
      NumeralFormula expected)
      throws SolverException, InterruptedException {
    assertThatFormula(rmgr.equal(f.apply(arg1, arg2), expected)).isSatisfiable();
    assertThat(mgr.getFormulaType(f.apply(arg1, arg2)).isRationalType()).isTrue();
  }

  /** Same as unary testOperation(), but we expect the result to be an integer term. */
  private void testIntegerOperation(
      Function<NumeralFormula, IntegerFormula> f, NumeralFormula arg, IntegerFormula expected)
      throws SolverException, InterruptedException {
    assertThatFormula(imgr.equal(f.apply(arg), expected)).isSatisfiable();
    assertThat(mgr.getFormulaType(f.apply(arg)).isIntegerType()).isTrue();
  }

  @Test
  public void negateTest() throws SolverException, InterruptedException {
    testOperation(rmgr::negate, imgr.makeNumber(1.5), rmgr.makeNumber(-1.0));
    testOperation(rmgr::negate, rmgr.makeNumber(1.5), rmgr.makeNumber(-1.5));
  }

  @Test
  public void addTest() throws SolverException, InterruptedException {
    testOperation(rmgr::add, imgr.makeNumber(2), imgr.makeNumber(1), rmgr.makeNumber(3.0));
    testOperation(rmgr::add, imgr.makeNumber(2), rmgr.makeNumber(1.5), rmgr.makeNumber(3.5));
    testOperation(rmgr::add, rmgr.makeNumber(1.5), imgr.makeNumber(2), rmgr.makeNumber(3.5));
    testOperation(rmgr::add, rmgr.makeNumber(1.5), rmgr.makeNumber(2.5), rmgr.makeNumber(4.0));
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
    testOperation(rmgr::subtract, imgr.makeNumber(2), imgr.makeNumber(1), rmgr.makeNumber(1.0));
    testOperation(rmgr::subtract, imgr.makeNumber(2), rmgr.makeNumber(1.5), rmgr.makeNumber(0.5));
    testOperation(rmgr::subtract, rmgr.makeNumber(1.5), imgr.makeNumber(2), rmgr.makeNumber(-0.5));
    testOperation(rmgr::subtract, rmgr.makeNumber(1.5), rmgr.makeNumber(0.5), rmgr.makeNumber(1.0));
  }

  @Test
  public void divideTest() throws SolverException, InterruptedException {
    testOperation(rmgr::divide, imgr.makeNumber(1), imgr.makeNumber(2), rmgr.makeNumber(0.5));
    testOperation(rmgr::divide, imgr.makeNumber(1), rmgr.makeNumber(2.0), rmgr.makeNumber(0.5));
    testOperation(rmgr::divide, rmgr.makeNumber(1.0), imgr.makeNumber(2), rmgr.makeNumber(0.5));
    testOperation(rmgr::divide, rmgr.makeNumber(1.0), rmgr.makeNumber(0.5), rmgr.makeNumber(2.0));
  }

  @Test
  public void multiplyTest() throws SolverException, InterruptedException {
    testOperation(rmgr::multiply, imgr.makeNumber(2), imgr.makeNumber(3), rmgr.makeNumber(6.0));
    testOperation(rmgr::multiply, imgr.makeNumber(2), rmgr.makeNumber(1.25), rmgr.makeNumber(2.5));
    testOperation(rmgr::multiply, rmgr.makeNumber(1.25), imgr.makeNumber(2), rmgr.makeNumber(2.5));
    testOperation(
        rmgr::multiply, rmgr.makeNumber(1.5), rmgr.makeNumber(2.5), rmgr.makeNumber(3.75));
  }

  @Test
  public void equalTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.equal(imgr.makeNumber(1.5), rmgr.makeNumber(1.0))).isSatisfiable();
    assertThatFormula(rmgr.equal(rmgr.makeNumber(1.0), imgr.makeNumber(1.5))).isSatisfiable();
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
    assertThatFormula(rmgr.greaterThan(imgr.makeNumber(1.5), rmgr.makeNumber(0.5))).isSatisfiable();
    assertThatFormula(rmgr.greaterThan(rmgr.makeNumber(1.5), imgr.makeNumber(1.5))).isSatisfiable();
  }

  @Test
  public void greaterOrEqualTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.greaterOrEquals(imgr.makeNumber(1.5), rmgr.makeNumber(1.0)))
        .isSatisfiable();
    assertThatFormula(rmgr.greaterOrEquals(rmgr.makeNumber(1.5), imgr.makeNumber(1.5)))
        .isSatisfiable();
  }

  @Test
  public void lessThanTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.lessThan(imgr.makeNumber(1.5), rmgr.makeNumber(1.5))).isSatisfiable();
    assertThatFormula(rmgr.lessThan(rmgr.makeNumber(0.5), imgr.makeNumber(1.5))).isSatisfiable();
  }

  @Test
  public void lessOrEqualTest() throws SolverException, InterruptedException {
    assertThatFormula(rmgr.lessOrEquals(imgr.makeNumber(1.5), rmgr.makeNumber(1.0)))
        .isSatisfiable();
    assertThatFormula(rmgr.lessOrEquals(rmgr.makeNumber(1.5), imgr.makeNumber(2.0)))
        .isSatisfiable();
  }

  @Test
  public void floorTest() throws SolverException, InterruptedException {
    requireRationalFloor();
    testIntegerOperation(rmgr::floor, imgr.makeNumber(1.0), imgr.makeNumber(1.0));
    testIntegerOperation(rmgr::floor, rmgr.makeNumber(1.5), imgr.makeNumber(1.0));
  }
}
