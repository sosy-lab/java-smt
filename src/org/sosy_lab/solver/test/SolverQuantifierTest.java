/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.fail;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.FormulaManagerFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.UnsafeFormulaManager;

@RunWith(Parameterized.class)
public class SolverQuantifierTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solverUnderTest;

  @Override
  protected Solvers solverToUse() {
    return solverUnderTest;
  }

  private IntegerFormula x;
  private ArrayFormula<IntegerFormula, IntegerFormula> a;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula a_at_x_eq_1;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula a_at_x_eq_0;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula forall_x_a_at_x_eq_0;

  @Before
  public void setUp() throws Exception {
    requireArrays();
    requireQuantifiers();

    x = imgr.makeVariable("x");
    a = amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);

    a_at_x_eq_1 = imgr.equal(amgr.select(a, x), imgr.makeNumber(1));
    a_at_x_eq_0 = imgr.equal(amgr.select(a, x), imgr.makeNumber(0));

    forall_x_a_at_x_eq_0 = qmgr.forall(ImmutableList.of(x), a_at_x_eq_0);
  }

  @Test
  public void testForallArrayConjunctUnsat() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) AND (b[123] = 1) is UNSAT
    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testForallArrayConjunctSat() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) AND (b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testForallArrayDisjunct1() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) AND (b[123] = 1 OR b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            bmgr.or(
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0))));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testForallArrayDisjunctSat2() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) OR (b[123] = 1) is SAT
    BooleanFormula f =
        bmgr.or(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testNotExistsArrayConjunct1() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) AND (b[123] = 1) is UNSAT
    BooleanFormula f =
        bmgr.and(
            Lists.newArrayList(
                bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1))));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testNotExistsArrayConjunct2() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) AND (b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testNotExistsArrayConjunct3() throws SolverException, InterruptedException {
    // (not exists x . b[x] = 0) AND (b[123] = 0) is UNSAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), a_at_x_eq_0)),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testNotExistsArrayDisjunct1() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) AND (b[123] = 1 OR b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            bmgr.or(
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0))));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testNotExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) OR (b[123] = 1) is SAT
    BooleanFormula f =
        bmgr.or(
            Lists.newArrayList(
                bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1))));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayConjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND (b[123] = 1) is SAT
    BooleanFormula f =
        bmgr.and(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayConjunct2() throws SolverException, InterruptedException {
    // (exists x . b[x] = 1) AND  (forall x . b[x] = 0) is UNSAT
    BooleanFormula f =
        bmgr.and(qmgr.exists(ImmutableList.of(x), a_at_x_eq_1), forall_x_a_at_x_eq_0);
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testExistsArrayConjunct3() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND  (forall x . b[x] = 0) is SAT
    BooleanFormula f =
        bmgr.and(qmgr.exists(ImmutableList.of(x), a_at_x_eq_0), forall_x_a_at_x_eq_0);
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayDisjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) OR  (forall x . b[x] = 1) is SAT
    BooleanFormula f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (exists x . b[x] = 1) OR (exists x . b[x] = 1) is SAT
    BooleanFormula f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_1),
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testContradiction() throws SolverException, InterruptedException {
    // forall x . x = x+1  is UNSAT
    BooleanFormula f =
        qmgr.forall(ImmutableList.of(x), imgr.equal(x, imgr.add(x, imgr.makeNumber(1))));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testSimple() throws SolverException, InterruptedException {
    // forall x . x+2 = x+1+1  is SAT
    BooleanFormula f =
        qmgr.forall(
            ImmutableList.of(x),
            imgr.equal(
                imgr.add(x, imgr.makeNumber(2)),
                imgr.add(imgr.add(x, imgr.makeNumber(1)), imgr.makeNumber(1))));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testEquals() {
    BooleanFormula f1 = qmgr.exists(ImmutableList.of(imgr.makeVariable("x")), a_at_x_eq_1);
    BooleanFormula f2 = qmgr.exists(ImmutableList.of(imgr.makeVariable("x")), a_at_x_eq_1);

    assertThat(f1).isEqualTo(f2);
  }

  @Test
  public void testIntrospectionForall() {
    assume()
        .withFailureMessage("Bug in Z3QuantifiedFormulaManager")
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    BooleanFormula forall = qmgr.forall(ImmutableList.of(x), a_at_x_eq_0);
    assertThat(qmgr.isQuantifier(forall)).isTrue();
    assertThat(qmgr.isForall(forall)).isTrue();
    assertThat(qmgr.isExists(forall)).isFalse();
    assertThat(qmgr.isBoundByQuantifier(forall)).isFalse();
    assertThat(qmgr.numQuantifierBound(forall)).isEqualTo(1);

    UnsafeFormulaManager umgr = mgr.getUnsafeFormulaManager();
    assertThat(umgr.isQuantification(forall)).isTrue();
    assertThat(umgr.getQuantifiedBody(forall)).isEqualTo(qmgr.getQuantifierBody(forall));
    assertThat(umgr.isAtom(forall)).isFalse();
    assertThat(umgr.isBoundVariable(forall)).isFalse();
    assertThat(umgr.isFreeVariable(forall)).isFalse();
    assertThat(umgr.isVariable(forall)).isFalse();
    assertThat(umgr.isNumber(forall)).isFalse();
    assertThat(umgr.isUF(forall)).isFalse();

    try {
      umgr.getArity(forall);
      fail("getArity for quantifier should fail");
    } catch (IllegalArgumentException expected) {
    }

    try {
      umgr.getName(forall);
      fail("getName for quantifier should fail");
    } catch (IllegalArgumentException expected) {
    }
  }

  @Test
  public void testIntrospectionExists() {
    assume()
        .withFailureMessage("Bug in Z3QuantifiedFormulaManager")
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    BooleanFormula exists = qmgr.exists(ImmutableList.of(x), a_at_x_eq_0);
    assertThat(qmgr.isQuantifier(exists)).isTrue();
    assertThat(qmgr.isForall(exists)).isFalse();
    assertThat(qmgr.isExists(exists)).isTrue();
    assertThat(qmgr.isBoundByQuantifier(exists)).isFalse();
    assertThat(qmgr.numQuantifierBound(exists)).isEqualTo(1);

    UnsafeFormulaManager umgr = mgr.getUnsafeFormulaManager();
    assertThat(umgr.isQuantification(exists)).isTrue();
    assertThat(umgr.getQuantifiedBody(exists)).isEqualTo(qmgr.getQuantifierBody(exists));
    assertThat(umgr.isAtom(exists)).isFalse();
    assertThat(umgr.isBoundVariable(exists)).isFalse();
    assertThat(umgr.isFreeVariable(exists)).isFalse();
    assertThat(umgr.isVariable(exists)).isFalse();
    assertThat(umgr.isNumber(exists)).isFalse();
    assertThat(umgr.isUF(exists)).isFalse();

    try {
      umgr.getArity(exists);
      fail("getArity for quantifier should fail");
    } catch (IllegalArgumentException expected) {
    }

    try {
      umgr.getName(exists);
      fail("getName for quantifier should fail");
    } catch (IllegalArgumentException expected) {
    }
  }
}
