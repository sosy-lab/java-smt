// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.BooleanType;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;

import com.google.common.truth.Truth;
import java.util.EnumSet;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

@RunWith(Parameterized.class)
public class SolverFormulaIODeclarationsTest extends SolverBasedTest0 {

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

  @Before
  public void checkThatSolverIsAvailable() {
    requireParser();
  }

  @Test
  public void parseDeclareInQueryTest1() {
    String query = "(declare-fun var () Bool)(assert var)";
    BooleanFormula formula = mgr.parse(query);
    Truth.assertThat(mgr.extractVariables(formula)).hasSize(1);
  }

  @Test
  public void parseDeclareInQueryTest2() {
    String query = "(declare-fun x () Int)(assert (= 0 x))";
    BooleanFormula formula = mgr.parse(query);
    Truth.assertThat(mgr.extractVariables(formula)).hasSize(1);
  }

  @Test
  public void parseDeclareInQueryTest3() {
    String query = "(declare-fun foo (Int Int) Bool)(assert (foo 1 2))";
    BooleanFormula formula = mgr.parse(query);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula)).hasSize(1);
  }

  @Test
  public void parseDeclareInQueryTest4() {
    String query = "(declare-fun x () Int)(declare-fun foo (Int Int) Bool)(assert (foo x 2))";
    BooleanFormula formula = mgr.parse(query);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula)).hasSize(2);
  }

  @Test
  public void parseDeclareAfterQueryTest1() {
    String query = "(declare-fun var () Bool)(assert var)";
    BooleanFormula formula = mgr.parse(query);
    BooleanFormula var = bmgr.makeVariable("var");
    Truth.assertThat(mgr.extractVariables(formula).values()).containsExactly(var);
  }

  @Test
  public void parseDeclareAfterQueryTest2() {
    String query = "(declare-fun x () Int)(assert (= 0 x))";
    BooleanFormula formula = mgr.parse(query);
    IntegerFormula var = imgr.makeVariable("x");
    Truth.assertThat(mgr.extractVariables(formula).values()).containsExactly(var);
  }

  @Test
  public void parseDeclareAfterQueryTest3() {
    String query = "(declare-fun foo (Int Int) Bool)(assert (foo 1 2))";
    BooleanFormula formula = mgr.parse(query);
    BooleanFormula calledFoo =
        fmgr.declareAndCallUF("foo", BooleanType, imgr.makeNumber(1), imgr.makeNumber(2));
    Truth.assertThat(mgr.extractVariablesAndUFs(formula).values()).containsExactly(calledFoo);
  }

  @Test
  public void parseDeclareAfterQueryTest4() {
    String query = "(declare-fun x () Int)(declare-fun foo (Int Int) Bool)(assert (foo 1 x))";
    BooleanFormula formula = mgr.parse(query);
    IntegerFormula var = imgr.makeVariable("x");
    BooleanFormula calledFoo = fmgr.declareAndCallUF("foo", BooleanType, imgr.makeNumber(1), var);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula).values()).containsExactly(var, calledFoo);
  }

  @Test
  public void parseDeclareNeverTest1() {
    String query = "(assert var)";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
  }

  @Test
  public void parseDeclareNeverTest2() {
    String query = "(assert (= 0 x))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
  }

  @Test
  public void parseDeclareNeverTest3() {
    String query = "(assert (foo 1 2))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
  }

  @Test
  public void parseDeclareNeverTest4() {
    String query = "(assert (foo 1 x))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
  }

  @Test
  public void parseDeclareBeforeTest() {
    String query = "(assert var)";
    BooleanFormula var = bmgr.makeVariable("var");
    BooleanFormula formula = mgr.parse(query);
    Truth.assertThat(mgr.extractVariables(formula).values()).containsExactly(var);
  }

  @Test
  public void parseDeclareRedundantTest1() {
    IntegerFormula var = imgr.makeVariable("x");
    String query = "(declare-fun x () Int)(declare-fun x () Int)(assert (= 0 x))";
    if (EnumSet.of(Solvers.PRINCESS, Solvers.Z3).contains(solverToUse())) {
      assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
    } else {
      // some solvers are more tolerant for identical symbols.
      BooleanFormula formula = mgr.parse(query);
      Truth.assertThat(mgr.extractVariables(formula).values()).containsExactly(var);
    }
  }

  @Test
  public void parseDeclareRedundantTest2() {
    IntegerFormula var =
        fmgr.declareAndCallUF("foo", IntegerType, imgr.makeNumber(1), imgr.makeNumber(2));
    String query =
        "(declare-fun foo (Int Int) Int)(declare-fun foo (Int Int) Int)(assert (= 0 (foo 1 2)))";
    if (EnumSet.of(Solvers.PRINCESS, Solvers.Z3).contains(solverToUse())) {
      assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
    } else {
      // some solvers are more tolerant for identical symbols.
      BooleanFormula formula = mgr.parse(query);
      Truth.assertThat(mgr.extractVariablesAndUFs(formula).values()).containsExactly(var);
    }
  }

  @Test
  public void parseDeclareConflictInQueryTest1() {
    String query = "(declare-fun x () Bool)(declare-fun x () Int)(assert (= 0 x))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
  }

  @Test
  public void parseDeclareConflictInQueryTest2() {
    String query = "(declare-fun x () Bool)(declare-fun x (Int Int) Bool)(assert (x 2 3))";
    if (Solvers.Z3 != solverToUse()) {
      assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
    }
  }

  @Test
  public void parseDeclareConflictInQueryTest3() {
    String query = "(declare-fun x (Int) Bool)(declare-fun x (Int) Int)(assert (x 0))";
    if (Solvers.Z3 != solverToUse()) {
      assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
    }
  }

  @Test
  public void parseDeclareConflictBeforeQueryTest() {
    @SuppressWarnings("unused")
    IntegerFormula var = imgr.makeVariable("x");
    String query = "(declare-fun x () Bool)(assert (= 0 x))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(query));
  }

  @Test
  public void parseDeclareConflictAfterQueryTest() {
    String query = "(declare-fun x () Bool)(assert x)";
    BooleanFormula formula = mgr.parse(query);
    Truth.assertThat(mgr.extractVariables(formula).values()).hasSize(1);
    if (!EnumSet.of(Solvers.PRINCESS, Solvers.Z3).contains(solverToUse())) {
      assertThrows(IllegalArgumentException.class, () -> imgr.makeVariable("x"));
    } else {
      Truth.assertThat(mgr.extractVariables(formula).values())
          .doesNotContain(imgr.makeVariable("x"));
    }
  }

  @Test
  public void parseDeclareOnceNotTwiceTest1() {
    String query1 = "(declare-fun x () Bool)(assert x)";
    String query2 = "(assert (not x))";
    BooleanFormula formula1 = mgr.parse(query1);
    Truth.assertThat(mgr.extractVariables(formula1).values()).hasSize(1);
    BooleanFormula formula2 = mgr.parse(query2);
    Truth.assertThat(mgr.extractVariables(formula2).values()).hasSize(1);
    Truth.assertThat(mgr.extractVariables(formula1)).isEqualTo(mgr.extractVariables(formula2));
  }

  @Test
  public void parseDeclareOnceNotTwiceTest2() {
    String query1 =
        "(declare-fun x () Bool)(declare-fun foo (Int Int) Bool)(assert (= (foo 1 2) x))";
    String query2 = "(assert (and (not x) (foo 3 4)))";
    BooleanFormula formula1 = mgr.parse(query1);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula1).values()).hasSize(2);
    BooleanFormula formula2 = mgr.parse(query2);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula2).values()).hasSize(2);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula1).keySet())
        .isEqualTo(mgr.extractVariablesAndUFs(formula2).keySet());
  }

  @Test
  public void parseDeclareOnceNotTwiceTest3() {
    String query1 = "(declare-fun x () Bool)(declare-fun y () Bool)(assert x)";
    String query2 = "(assert y)";
    BooleanFormula formula1 = mgr.parse(query1);
    Truth.assertThat(mgr.extractVariablesAndUFs(formula1).values()).hasSize(1);
    if (Solvers.Z3 == solverToUse()) {
      // "y" is unknown for the second query.
      assertThrows(IllegalArgumentException.class, () -> mgr.parse(query2));
    } else {
      BooleanFormula formula2 = mgr.parse(query2);
      Truth.assertThat(mgr.extractVariablesAndUFs(formula2).values()).hasSize(1);
    }
  }
}
