// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import java.util.List;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class ParserTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Before
  public void setUp() {
    requireParser();
  }

  @Test
  public void testParseAll_valid_simpleBoolean() {
    String smt = "(assert true)";
    assertThat(mgr.parseAll(smt)).containsExactly(bmgr.makeTrue());
  }

  @Test
  public void testParseAll_valid_simpleInteger() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (= x 1))";
    assertThat(mgr.parseAll(smt))
        .containsExactly(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
  }

  @Test
  public void testParseAll_valid_defineFun() throws SolverException, InterruptedException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support parsing function definitions", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.SMTINTERPOL);

    String smt =
        "(define-fun f ((x Int)) Int (+ x 1))"
            + "(assert true)"
            + "(declare-fun y1 () Int)"
            + "(declare-fun y2 () Int)"
            + "(assert (= (f y1) 2))"
            + "(define-fun g ((x Int)) Int (+ x 3))"
            + "(assert (= (g y2) 2))"
            + "(declare-fun y3 () Int)"
            + "(declare-fun y4 () Int)"
            + "(assert (= (g y3) 2))"
            + "(define-fun h ((x Int)) Int (+ x 5))"
            + "(assert (= (h y4) 2))";
    List<BooleanFormula> parsed = mgr.parseAll(smt);
    assertThat(parsed).hasSize(5);
    assertThatFormula(parsed.get(0)).isEquivalentTo(bmgr.makeTrue());
    assertThatFormula(parsed.get(1))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y1"), imgr.makeNumber(1)));
    assertThatFormula(parsed.get(2))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y2"), imgr.makeNumber(-1)));
    assertThatFormula(parsed.get(3))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y3"), imgr.makeNumber(-1)));
    assertThatFormula(parsed.get(4))
        .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("y4"), imgr.makeNumber(-3)));
  }

  @Test
  public void testParseAll_valid_multipleAssertions() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (> x 0))(assert (< x 10))";
    BooleanFormula gt = imgr.greaterThan(imgr.makeVariable("x"), imgr.makeNumber(0));
    BooleanFormula lt = imgr.lessThan(imgr.makeVariable("x"), imgr.makeNumber(10));
    assertThat(mgr.parseAll(smt)).containsExactly(gt, lt).inOrder();
  }

  @Test
  public void testParseAll_valid_differentTypes() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(declare-fun y () Bool)(assert (= x 1))(assert y)";
    BooleanFormula intEq = imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1));
    BooleanFormula boolY = bmgr.makeVariable("y");
    assertThat(mgr.parseAll(smt)).containsExactly(intEq, boolY).inOrder();
  }

  @Test
  public void testParseAll_valid_functionApplication() {
    requireIntegers();
    String smt = "(declare-fun f (Int) Int)(declare-fun x () Int)(assert (= (f x) 1))";
    IntegerFormula x = imgr.makeVariable("x");
    assertThat(mgr.parseAll(smt))
        .containsExactly(
            imgr.equal(fmgr.declareAndCallUF("f", FormulaType.IntegerType, x), imgr.makeNumber(1)));
  }

  @Test
  public void testParseAll_valid_bitvector() throws SolverException, InterruptedException {
    requireBitvectors();
    String smt = "(declare-fun x () (_ BitVec 8))(assert (= x #x01))";
    List<BooleanFormula> parsed = mgr.parseAll(smt);
    assertThat(parsed).hasSize(1);
    assertThatFormula(Iterables.getOnlyElement(parsed))
        .isEquisatisfiableTo(bvmgr.equal(bvmgr.makeVariable(8, "x"), bvmgr.makeBitvector(8, 1)));
  }

  @Test
  public void testParseAll_valid_quantifier() {
    requireQuantifiers();
    requireIntegers();
    String smt = "(declare-fun p (Int) Bool)(assert (forall ((x Int)) (p x)))";
    // NOTE: This test might be tricky as forall parsing can be complex.
    // For now, we will just assert that it doesn't throw an exception and returns a formula.
    // A more robust check would involve comparing the structure of the formula.
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void testParseAll_valid_string() throws SolverException, InterruptedException {
    requireStrings();
    assume()
        .withMessage("Solver %s does not support parsing strings", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    String smt = "(declare-fun s () String)(assert (= s \"hello\"))";
    List<BooleanFormula> parsed = mgr.parseAll(smt);
    assertThat(parsed).hasSize(1);
    assertThatFormula(Iterables.getOnlyElement(parsed))
        .isEquisatisfiableTo(smgr.equal(smgr.makeVariable("s"), smgr.makeString("hello")));
  }

  @Test
  public void testParseAll_valid_floatingPointFromInt() {
    requireFloats();
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (= x 1.0))";
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void testParseAll_valid_floatingPointFromReal() {
    requireFloats();
    requireRationals();
    String smt = "(declare-fun x () Real)(assert (= x 1.0))";
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void testParseAll_valid_complexNested() {
    requireIntegers();
    String smt =
        "(declare-fun x () Int)(declare-fun y () Int)(assert (or (= x 1) (and (> y 0) (< y 10))))";
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula eqX = imgr.equal(x, imgr.makeNumber(1));
    BooleanFormula gtY = imgr.greaterThan(y, imgr.makeNumber(0));
    BooleanFormula ltY = imgr.lessThan(y, imgr.makeNumber(10));
    BooleanFormula and = bmgr.and(gtY, ltY);
    BooleanFormula or = bmgr.or(eqX, and);
    assertThat(mgr.parseAll(smt)).containsExactly(or);
  }

  @Test
  public void testParseAll_valid_letBinding() {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (let ((a x)) (= a 1)))";
    // For now, just check if it parses without error and returns a formula.
    // Detailed check of let-binding expansion might be solver-dependent.
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isInstanceOf(BooleanFormula.class);
  }

  @Test
  public void testParseAll_invalid_syntaxError() {
    String smt = "(assert (= x 1)"; // Missing closing parenthesis
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void testParseAll_invalid_undeclaredVariable() {
    String smt = "(assert (= x 1))"; // 'x' not declared
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void testParseAll_invalid_typeMismatch() throws SolverException, InterruptedException {
    requireIntegers();
    String smt = "(declare-fun x () Int)(assert (= x true))"; // Int vs Bool
    if (solverToUse() == Solvers.Z3) {
      // Z3 is more lenient and allows this, treating 'true' as 1 and 'false' as 0.
      List<BooleanFormula> parsed = mgr.parseAll(smt);
      assertThat(parsed).hasSize(1);
      assertThatFormula(Iterables.getOnlyElement(parsed))
          .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
    } else {
      assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
    }
  }

  @Test
  public void testParseAll_invalid_unknownCommandWithAssertion() {
    String smt = "(unknown-command)(assert true)";
    assertThat(mgr.parseAll(smt)).hasSize(1);
    assertThat(mgr.parseAll(smt).get(0)).isEqualTo(bmgr.makeTrue());
  }

  @Test
  public void testParseAll_invalid_unknownCommand() {
    String smt = "(unknown-command)";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void testParseAll_invalid_emptyString() {
    String smt = "";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void testParseAll_invalid_emptyString2() {
    String smt = "   ";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void testParseAll_invalid_emptyString3() {
    String smt = "\n\t  \n";
    assertThat(mgr.parseAll(smt)).isEmpty();
  }

  @Test
  public void testParseAll_invalid_incorrectFunctionArity() {
    requireIntegers();
    String smt = "(declare-fun f (Int) Int)(assert (f))"; // f expects 1 arg, got 0
    assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
  }

  @Test
  public void testParseAll_invalid_reservedKeyword() throws SolverException, InterruptedException {
    requireIntegers();
    // 'assert' is a reserved keyword, cannot be used as a function name in most solvers
    String smt = "(declare-fun assert () Int)(assert (= assert 1))";
    if (ImmutableList.of(Solvers.Z3, Solvers.CVC5).contains(solverToUse())) {
      List<BooleanFormula> parsed = mgr.parseAll(smt);
      assertThat(parsed).hasSize(1);
      assertThatFormula(Iterables.getOnlyElement(parsed))
          .isEquisatisfiableTo(imgr.equal(imgr.makeVariable("assert"), imgr.makeNumber(1)));
    } else {
      assertThrows(IllegalArgumentException.class, () -> mgr.parseAll(smt));
    }
  }
}
