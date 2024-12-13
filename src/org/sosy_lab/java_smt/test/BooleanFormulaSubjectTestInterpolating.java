// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.ExpectFailure.assertThat;
import static org.sosy_lab.java_smt.test.BooleanFormulaSubject.booleanFormulasOf;

import com.google.common.base.Throwables;
import com.google.common.truth.ExpectFailure;
import com.google.common.truth.ExpectFailure.SimpleSubjectBuilderCallback;
import com.google.common.truth.SimpleSubjectBuilder;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedInterpolatingSolverBasedTest0;

/**
 * Uses bitvector theory if there is no integer theory available. Notice: Boolector does not support
 * bitvectors length 1.
 */
public class BooleanFormulaSubjectTestInterpolating
    extends ParameterizedInterpolatingSolverBasedTest0 {

  private BooleanFormula simpleFormula;
  private BooleanFormula contradiction;
  private BooleanFormula tautology;

  @Before
  public void setupFormulas() {
    if (imgr != null) {
      simpleFormula = imgr.equal(imgr.makeVariable("a"), imgr.makeNumber(1));
      contradiction =
          bmgr.and(simpleFormula, imgr.equal(imgr.makeVariable("a"), imgr.makeNumber(2)));
    } else {
      simpleFormula = bvmgr.equal(bvmgr.makeVariable(2, "a"), bvmgr.makeBitvector(2, 1));
      contradiction =
          bmgr.and(
              simpleFormula, bvmgr.equal(bvmgr.makeVariable(2, "a"), bvmgr.makeBitvector(2, 2)));
    }
    tautology = bmgr.or(simpleFormula, bmgr.not(simpleFormula));
  }

  @Test
  public void testIsTriviallySatisfiableYes() throws SolverException, InterruptedException {
    assertThatFormula(bmgr.makeTrue()).isSatisfiable();
  }

  @Test
  public void testIsTriviallySatisfiableNo() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(bmgr.makeFalse()).isSatisfiable());
    assertThat(failure).factValue("but was").isEqualTo("trivially unsatisfiable");
  }

  @Test
  public void testIsSatisfiableYes() throws SolverException, InterruptedException {
    assertThatFormula(simpleFormula).isSatisfiable();
  }

  @Test
  public void testIsSatisfiableNo() {
    requireUnsatCore();
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(contradiction).isSatisfiable());
    assertThat(failure).factValue("which has unsat core").isNotEmpty();
  }

  @Test
  public void testIsTriviallyUnSatisfiableYes() throws SolverException, InterruptedException {
    assertThatFormula(bmgr.makeFalse()).isUnsatisfiable();
  }

  @Test
  public void testIsTriviallyUnSatisfiableNo() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(bmgr.makeTrue()).isUnsatisfiable());
    assertThat(failure).factValue("but was").isEqualTo("trivially satisfiable");
  }

  @Test
  public void testIsUnsatisfiableYes() throws SolverException, InterruptedException {
    assertThatFormula(contradiction).isUnsatisfiable();
  }

  @Test
  public void testIsUnsatisfiableNo() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(simpleFormula).isUnsatisfiable());
    requireModel();
    assertThat(failure).factValue("which has model").isNotEmpty();
  }

  @Test
  public void testIsTriviallyTautologicalYes() throws SolverException, InterruptedException {
    assertThatFormula(bmgr.makeTrue()).isTautological();
  }

  @Test
  public void testIsTriviallyTautologicalNo() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(bmgr.makeFalse()).isTautological());
    assertThat(failure).factValue("but was").isEqualTo("trivially unsatisfiable");
  }

  @Test
  public void testIsTautologicalYes() throws SolverException, InterruptedException {
    assertThatFormula(tautology).isTautological();
  }

  @Test
  public void testIsTautologicalNo1() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(simpleFormula).isTautological());
    requireModel();
    assertThat(failure).factValue("which has model").isNotEmpty();
  }

  @Test
  public void testIsTautologicalNo2() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(contradiction).isTautological());
    requireModel();
    assertThat(failure).factValue("which has model").isNotEmpty();
  }

  @Test
  public void testIsEquivalentToYes() throws SolverException, InterruptedException {
    BooleanFormula simpleFormula2;
    if (imgr != null) {
      simpleFormula2 =
          imgr.equal(imgr.makeVariable("a"), imgr.add(imgr.makeNumber(0), imgr.makeNumber(1)));
    } else {
      simpleFormula2 =
          bvmgr.equal(
              bvmgr.makeVariable(2, "a"),
              bvmgr.add(bvmgr.makeBitvector(2, 0), bvmgr.makeBitvector(2, 1)));
    }
    assertThatFormula(simpleFormula).isEquivalentTo(simpleFormula2);
  }

  @Test
  public void testIsEquivalentToNo() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(simpleFormula).isEquivalentTo(tautology));
    requireModel();
    assertThat(failure).factValue("which has model").isNotEmpty();
  }

  @Test
  public void testIsEquisatisfiableToYes() throws SolverException, InterruptedException {
    assertThatFormula(simpleFormula).isEquisatisfiableTo(tautology);
  }

  @Test
  public void testIsEquisatisfiableToNo() {
    BooleanFormula simpleFormula2;
    if (imgr != null) {
      simpleFormula2 = imgr.equal(imgr.makeVariable("a"), imgr.makeNumber("2"));
    } else {
      simpleFormula2 = bvmgr.equal(bvmgr.makeVariable(2, "a"), bvmgr.makeVariable(2, "2"));
    }
    AssertionError failure =
        expectFailure(
            whenTesting -> whenTesting.that(simpleFormula).isEquisatisfiableTo(simpleFormula2));
    requireModel();
    assertThat(failure).factValue("which has model").isNotEmpty();
  }

  @Test
  public void testImpliesYes() throws SolverException, InterruptedException {
    assertThatFormula(simpleFormula).implies(tautology);
  }

  @Test
  public void testImpliesNo() {
    AssertionError failure =
        expectFailure(whenTesting -> whenTesting.that(tautology).implies(simpleFormula));
    requireModel();
    assertThat(failure).factValue("which has model").isNotEmpty();
  }

  private AssertionError expectFailure(ExpectFailureCallback expectFailureCallback) {
    return ExpectFailure.expectFailureAbout(booleanFormulasOf(context), expectFailureCallback);
  }

  /** Variant of {@link SimpleSubjectBuilderCallback} that allows checked exception. */
  private interface ExpectFailureCallback
      extends SimpleSubjectBuilderCallback<BooleanFormulaSubject, BooleanFormula> {

    void invokeAssertionUnchecked(
        SimpleSubjectBuilder<BooleanFormulaSubject, BooleanFormula> pWhenTesting) throws Exception;

    @Override
    default void invokeAssertion(
        SimpleSubjectBuilder<BooleanFormulaSubject, BooleanFormula> pWhenTesting) {
      try {
        invokeAssertionUnchecked(pWhenTesting);
      } catch (Exception e) {
        Throwables.throwIfUnchecked(e);
        throw new RuntimeException(e);
      }
    }
  }
}
