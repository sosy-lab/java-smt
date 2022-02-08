// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import io.github.cvc5.api.CVC5ApiException;
import io.github.cvc5.api.Kind;
import io.github.cvc5.api.Result;
import io.github.cvc5.api.RoundingMode;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.util.Arrays;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

/*
 * Please note that CVC5 does not have a native variable cache!
 * Each variable created is a new one with a new internal id, even if they are named the same.
 * As a result, checking equality on 2 formulas that are build with new variables
 *  that are named the same results in false!
 * Additionally, CVC5 only supports quantifier elimination for LIA and LRA.
 * However, it might run endlessly in some cases if you try quantifier elimination on array
 * theories!
 */
public class CVC5NativeAPITest {

  private static final String INVALID_GETVALUE_STRING =
      "Cannot get-value unless immediately preceded by SAT/NOT_ENTAILED or UNKNOWN response.";

  private static final String INVALID_MODEL_STRING =
      "Cannot get model unless immediately preceded by SAT/NOT_ENTAILED or UNKNOWN response.";

  private Term x;
  private Term array;
  private Term aAtxEq0;
  private Term aAtxEq1;

  private Solver solver;

  @Before
  public void createEnvironment() throws CVC5ApiException {
    solver = new Solver();
    // Set the logic
    solver.setLogic("ALL");

    // options
    solver.setOption("produce-models", "true");
    solver.setOption("finite-model-find", "true");
    solver.setOption("sets-ext", "true");
    solver.setOption("output-language", "smtlib2");
  }

  @After
  public void freeEnvironment() {
    solver.close();
  }

  @Test
  public void checkSimpleUnsat() {

    solver.assertFormula(solver.mkBoolean(false));
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleSat() {
    solver.assertFormula(solver.mkBoolean(true));
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleEqualitySat() {
    Term one = solver.mkInteger(1);
    Term assertion = solver.mkTerm(Kind.EQUAL, one, one);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleEqualityUnsat() {
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);
    Term assertion = solver.mkTerm(Kind.EQUAL, zero, one);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleInequalityUnsat() {
    Term one = solver.mkInteger(1);
    Term assertion = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, one, one));
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleInequalitySat() {
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);
    Term assertion = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, zero, one));
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleLIAEqualitySat() {
    Term one = solver.mkInteger(1);
    Term two = solver.mkInteger(2);
    Term assertion = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, one, one), two);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleLIAEqualityUnsat() {
    Term one = solver.mkInteger(1);
    Term assertion = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, one, one), one);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLIASat() {
    // x + y = 4 AND x * y = 4
    Term four = solver.mkInteger(4);
    Term varX = solver.mkVar(solver.getIntegerSort(), "x");
    Term varY = solver.mkVar(solver.getIntegerSort(), "y");
    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), four);
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, varX, varY), four);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    assertThat(getInt(varX) + getInt(varY)).isEqualTo(4);
    assertThat(getInt(varX) * getInt(varY)).isEqualTo(4);
  }

  /** Helper to get to int values faster. */
  private int getInt(Term cvc5Term) {
    String string = solver.getValue(cvc5Term).toString();
    return Integer.parseInt(string);
  }

  @Test
  public void checkSimpleLIAUnsat() {
    // x + y = 1 AND x * y = 1
    Term one = solver.mkInteger(1);
    Term varX = solver.mkVar(solver.getIntegerSort(), "x");
    Term varY = solver.mkVar(solver.getIntegerSort(), "y");
    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), one);
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, varX, varY), one);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkLIAModel() {
    // 1 + 2 = var
    // it follows that var = 3
    Term one = solver.mkInteger(1);
    Term two = solver.mkInteger(2);
    Term var = solver.mkVar(solver.getIntegerSort());
    Term assertion = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, one, two), var);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isTrue();
    Term assertionValue = solver.getValue(assertion);
    assertThat(assertionValue.toString()).isEqualTo("true");
    assertThat(solver.getValue(var).toString()).isEqualTo("3");
  }

  @Test
  public void checkSimpleLIRAUnsat2() {
    // x + y = 4 AND x * y = 4
    Term threeHalf = solver.mkReal(3, 2);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term varY = solver.mkVar(solver.getRealSort(), "y");
    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), threeHalf);
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, varX, varY), threeHalf);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLIRASat() {
    // x + y = 8/5 AND x > 0 AND y > 0 AND x < 8/5 AND y < 8/5
    Term zero = solver.mkReal(0);
    Term eightFifth = solver.mkReal(8, 5);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term varY = solver.mkVar(solver.getRealSort(), "y");
    Term assertion1 = solver.mkTerm(Kind.GT, varX, zero);
    Term assertion2 = solver.mkTerm(Kind.GT, varY, zero);
    Term assertion3 = solver.mkTerm(Kind.LT, varX, eightFifth);
    Term assertion4 = solver.mkTerm(Kind.LT, varY, eightFifth);
    Term assertion5 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, varX, varY), eightFifth);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    solver.assertFormula(assertion3);
    solver.assertFormula(assertion4);
    solver.assertFormula(assertion5);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Real uses the same operators as int (plain plus, mult etc.) */
  @Test
  public void checkSimpleLRASat() {
    // x * y = 8/5 AND x < 4/5
    Term fourFifth = solver.mkReal(4, 5);
    Term eightFifth = solver.mkReal(8, 5);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term varY = solver.mkVar(solver.getRealSort(), "y");

    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), eightFifth);
    Term assertion2 = solver.mkTerm(Kind.LT, varX, fourFifth);

    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Exponents may only be natural number constants. */
  @Test
  public void checkSimplePow() {
    // x ^ 2 = 4 AND x ^ 3 = 8
    Term two = solver.mkReal(2);
    Term three = solver.mkReal(3);
    Term four = solver.mkReal(4);
    Term eight = solver.mkReal(8);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.POW, varX, two), four);
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.POW, varX, three), eight);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleFPSat() throws CVC5ApiException {
    // x * y = 1/4
    Term rmTerm = solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
    Term oneFourth = solver.mkFloatingPoint(8, 24, solver.mkReal(1, 4));

    Term varX = solver.mkVar(solver.mkFloatingPointSort(8, 24), "x");
    Term varY = solver.mkVar(solver.mkFloatingPointSort(8, 24), "y");
    Term assertion1 =
        solver.mkTerm(
            Kind.FLOATINGPOINT_EQ,
            solver.mkTerm(Kind.FLOATINGPOINT_MULT, rmTerm, varX, varY),
            oneFourth);

    solver.assertFormula(assertion1);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleFPUnsat() throws CVC5ApiException {
    // x * y = 1/4 AND x > 0 AND y < 0
    Term rmTerm = solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
    Term oneFourth = solver.mkFloatingPoint(8, 24, solver.mkReal(1, 4));

    Term zero = solver.mkFloatingPoint(8, 24, solver.mkReal(0));

    Term varX = solver.mkVar(solver.mkFloatingPointSort(8, 24), "x");
    Term varY = solver.mkVar(solver.mkFloatingPointSort(8, 24), "y");
    Term assertion1 =
        solver.mkTerm(
            Kind.FLOATINGPOINT_EQ,
            solver.mkTerm(Kind.FLOATINGPOINT_MULT, rmTerm, varX, varY),
            oneFourth);
    Term assertion2 = solver.mkTerm(Kind.FLOATINGPOINT_GT, varX, zero);
    Term assertion3 = solver.mkTerm(Kind.FLOATINGPOINT_LT, varY, zero);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    solver.assertFormula(assertion3);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLRAUnsat() {
    // x + y = x * y AND x - 1 = 0
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term varY = solver.mkVar(solver.getRealSort(), "y");
    Term assertion1 =
        solver.mkTerm(
            Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), solver.mkTerm(Kind.PLUS, varX, varY));
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MINUS, varX, one), zero);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLRAUnsat2() {
    // x + y = 3/2 AND x * y = 3/2
    Term threeHalf = solver.mkReal(3, 2);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term varY = solver.mkVar(solver.getRealSort(), "y");
    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), threeHalf);
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, varX, varY), threeHalf);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleIncrementalSolving() throws CVC5ApiException {
    // x + y = 3/2 AND x * y = 3/2 (AND x - 1 = 0)
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);
    Term threeHalf = solver.mkReal(3, 2);
    Term varX = solver.mkVar(solver.getRealSort(), "x");
    Term varY = solver.mkVar(solver.getRealSort(), "y");
    // this alone is SAT
    Term assertion1 =
        solver.mkTerm(
            Kind.EQUAL, solver.mkTerm(Kind.MULT, varX, varY), solver.mkTerm(Kind.PLUS, varX, varY));
    // both 2 and 3 make it UNSAT (either one)
    Term assertion2 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, varX, varY), threeHalf);
    Term assertion3 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MINUS, varX, one), zero);
    solver.push();
    solver.assertFormula(assertion1);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    solver.push();
    solver.assertFormula(assertion2);
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
    solver.pop();
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    solver.push();
    solver.assertFormula(assertion3);
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
    solver.pop();
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Note that model and getValue are seperate! */
  @Test
  public void checkInvalidModelGetValue() {
    Term assertion = solver.mkBoolean(false);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isFalse();
    Exception e =
        assertThrows(io.github.cvc5.api.CVC5ApiException.class, () -> solver.getValue(assertion));
    assertThat(e.toString()).contains(INVALID_GETVALUE_STRING);
  }

  /** The getModel() call needs an array of sorts and terms. */
  @Test
  public void checkGetModel() {
    Term assertion = solver.mkBoolean(false);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isFalse();
    Sort[] sorts = new Sort[] {solver.getBooleanSort()};
    Term[] terms = new Term[] {assertion};
    String model = solver.getModel(sorts, terms);
    assertThat(model.toString()).contains(INVALID_MODEL_STRING);
  }

  /**
   * The getModel() call needs an array of sorts and terms. This tests what happens if you put empty
   * arrays into it.
   */
  @Test
  public void checkInvalidGetModel() {
    Term assertion = solver.mkBoolean(false);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isFalse();
    Sort[] sorts = new Sort[1];
    Term[] terms = new Term[1];
    String model = solver.getModel(sorts, terms);
    assertThat(model.toString()).contains(INVALID_MODEL_STRING);
  }

  /** It does not matter if you take an int or array or bv here, all result in the same error. */
  @Test
  public void checkInvalidTypeOperationsAssert() throws CVC5ApiException {
    Sort bvSort = solver.mkBitVectorSort(16);
    Term bvVar = solver.mkConst(bvSort, "bla");
    Term assertion = solver.mkTerm(Kind.AND, bvVar, bvVar);

    Exception e =
        assertThrows(
            io.github.cvc5.api.CVC5ApiException.class, () -> solver.assertFormula(assertion));
    assertThat(e.toString()).contains("expecting a Boolean subTermession");
  }

  /** It does not matter if you take an int or array or bv here, all result in the same error. */
  @Test
  public void checkInvalidTypeOperationsCheckSat() throws CVC5ApiException {
    Sort bvSort = solver.mkBitVectorSort(16);
    Term bvVar = solver.mkVar(bvSort, "bla");
    Term assertion = solver.mkTerm(Kind.AND, bvVar, bvVar);
    solver.assertFormula(assertion);

    Exception e = assertThrows(io.github.cvc5.api.CVC5ApiException.class, () -> solver.checkSat());
    assertThat(e.toString()).contains("expecting a Boolean subTermession");
  }

  @Test
  public void checkBvInvalidZeroWidthAssertion() throws CVC5ApiException {
    Term bvOne = solver.mkBitVector(0, 1);
    Term assertion = solver.mkTerm(Kind.EQUAL, bvOne, bvOne);

    Exception e =
        assertThrows(
            io.github.cvc5.api.CVC5ApiException.class, () -> solver.assertFormula(assertion));
    assertThat(e.toString()).contains("constant of size 0");
  }

  @Test
  public void checkBvInvalidNegativeWidthCheckAssertion() throws CVC5ApiException {
    Term bvOne = solver.mkBitVector(-1, 1);
    Term assertion = solver.mkTerm(Kind.EQUAL, bvOne, bvOne);

    Exception e =
        assertThrows(
            io.github.cvc5.api.CVC5ApiException.class, () -> solver.assertFormula(assertion));
    assertThat(e.toString()).contains("constant of size 0");
  }

  @Test
  public void checkSimpleBvEqualitySat() throws CVC5ApiException {
    // 1 + 0 = 1 with bitvectors
    Term bvOne = solver.mkBitVector(16, 1);
    Term bvZero = solver.mkBitVector(16, 0);
    Term assertion = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, bvZero, bvOne), bvOne);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleBvEqualityUnsat() throws CVC5ApiException {
    // 0 + 1 = 2 UNSAT with bitvectors
    Term bvZero = solver.mkBitVector(16, 0);
    Term bvOne = solver.mkBitVector(16, 1);
    Term bvTwo = solver.mkBitVector(16, 2);
    Term assertion = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, bvZero, bvOne), bvTwo);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleBvUnsat() throws CVC5ApiException {
    // var + 1 = 0 & var < max bitvector & var > 0; both < and > signed
    // Because of bitvector nature its UNSAT now

    Term bvVar = solver.mkConst(solver.mkBitVectorSort(16), "bvVar");
    Term bvOne = solver.mkBitVector(16, 1);
    Term bvZero = solver.mkBitVector(16, 0);
    Term assertion1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.PLUS, bvVar, bvOne), bvZero);
    // mkMaxSigned(16);
    Term assertion2 = solver.mkTerm(Kind.BITVECTOR_SLT, bvVar, makeMaxCVC5Bitvector(16, true));
    Term assertion3 = solver.mkTerm(Kind.BITVECTOR_SGT, bvVar, bvZero);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    solver.assertFormula(assertion3);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  /*
   * CVC5 fails some easy quantifier tests.
   */
  @Test
  public void checkQuantifierExistsIncomplete() {
    // (not exists x . not b[x] = 0) AND (b[123] = 0) is SAT

    setupArrayQuant();
    Term zero = solver.mkInteger(0);

    Term xBound = solver.mkVar(solver.getIntegerSort(), "x");
    Term quantifiedVars = solver.mkTerm(Kind.VARIABLE_LIST, xBound);
    Term aAtxEq0s = aAtxEq0.substitute(x, xBound);
    Term exists = solver.mkTerm(Kind.EXISTS, quantifiedVars, solver.mkTerm(Kind.NOT, aAtxEq0s));
    Term notExists = solver.mkTerm(Kind.NOT, exists);

    Term select123 = solver.mkTerm(Kind.SELECT, array, solver.mkReal(123));
    Term selectEq0 = solver.mkTerm(Kind.EQUAL, select123, zero);
    Term assertion = solver.mkTerm(Kind.AND, notExists, selectEq0);

    // assertFormula has a return value, check?
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    // CVC5 fails this test as incomplete
    assertThat(satCheck.isSatUnknown()).isTrue();
    assertThat(satCheck.getUnknownExplanation()).isEqualTo(Result.UnknownExplanation.INCOMPLETE);
  }

  @Test
  public void checkQuantifierEliminationLIA() {
    // build formula: (forall x . ((x < 5) | (7 < x + y)))
    // quantifier-free equivalent: (2 < y) or (>= y 3)
    setupArrayQuant();

    Term three = solver.mkReal(3);
    Term five = solver.mkReal(5);
    Term seven = solver.mkReal(7);

    Term y = solver.mkVar(solver.getIntegerSort(), "y");

    Term first = solver.mkTerm(Kind.LT, x, five);
    Term second = solver.mkTerm(Kind.LT, seven, solver.mkTerm(Kind.PLUS, x, y));
    Term body = solver.mkTerm(Kind.OR, first, second);

    Term xBound = solver.mkVar(solver.getIntegerSort(), "xBound");
    Term quantifiedVars = solver.mkTerm(Kind.VARIABLE_LIST, xBound);

    Term bodySubst = body.substitute(x, xBound);
    Term assertion = solver.mkTerm(Kind.FORALL, quantifiedVars, bodySubst);

    Term result = solver.getQuantifierElimination(assertion);

    Term resultCheck = solver.mkTerm(Kind.GEQ, y, three);
    assertThat(result.toString()).isEqualTo(resultCheck.toString());
  }

  @Test
  public void checkQuantifierWithUf() {
    Term var = solver.mkVar(solver.getIntegerSort(), "var");
    // start with a normal, free variable!
    Term boundVar = solver.mkVar(solver.getIntegerSort(), "boundVar");
    Term varIsOne = solver.mkTerm(Kind.EQUAL, var, solver.mkInteger(1));
    // try not to use 0 as this is the default value for CVC5 models
    Term boundVarIsTwo = solver.mkTerm(Kind.EQUAL, boundVar, solver.mkInteger(2));
    Term boundVarIsOne = solver.mkTerm(Kind.EQUAL, boundVar, solver.mkInteger(1));

    String func = "func";
    Sort intSort = solver.getIntegerSort();

    Sort ufSort = solver.mkFunctionSort(intSort, intSort);
    Term uf = solver.mkVar(ufSort, func);
    Term funcAtBoundVar = solver.mkTerm(Kind.APPLY_UF, uf, boundVar);

    Term body =
        solver.mkTerm(Kind.AND, boundVarIsTwo, solver.mkTerm(Kind.EQUAL, var, funcAtBoundVar));

    // This is the bound variable used for boundVar
    Term boundVarBound = solver.mkVar(solver.getIntegerSort(), "boundVarBound");
    Term quantifiedVars = solver.mkTerm(Kind.VARIABLE_LIST, boundVarBound);
    // Subst all boundVar variables with the bound version
    Term bodySubst = body.substitute(boundVar, boundVarBound);
    Term quantFormula = solver.mkTerm(Kind.EXISTS, quantifiedVars, bodySubst);

    // var = 1 & boundVar = 1 & exists boundVar . ( boundVar = 2 & f(boundVar) = var )
    Term overallFormula = solver.mkTerm(Kind.AND, varIsOne, boundVarIsOne, quantFormula);

    solver.assertFormula(overallFormula);

    Result satCheck = solver.checkSat();

    // SAT
    assertThat(satCheck.isSat()).isTrue();

    // check Model
    // var = 1 & boundVar = 1 & exists boundVar . ( boundVar = 2 & f(2) = 1 )
    // It seems like CVC5 can't return quantified variables,
    // therefore we can't get a value for the uf!
    assertThat(solver.getValue(var).toString()).isEqualTo("1");
    assertThat(solver.getValue(boundVar).toString()).isEqualTo("1");

    assertThat(solver.getValue(funcAtBoundVar).toString()).isEqualTo("1");
    assertThat(solver.getValue(boundVarBound).toString()).isEqualTo("boundVar");
  }

  /**
   * CVC5 does not support Array quantifier elimination. This is expected to fail! But it runs
   * endlessly. So we can check interruption on it. Currently CVC5 does not support interruption.
   */
  @Ignore
  @Test
  public void checkInterruptBehaviour() {
    setupArrayQuant();
    Term body = solver.mkTerm(Kind.OR, aAtxEq0, aAtxEq1);

    Term xBound = solver.mkVar(solver.getIntegerSort(), "x_b");
    Term quantifiedVars = solver.mkTerm(Kind.VARIABLE_LIST, xBound);
    Term bodySubst = body.substitute(x, xBound);
    Term assertion = solver.mkTerm(Kind.FORALL, quantifiedVars, bodySubst);

    Thread t =
        new Thread(
            () -> {
              try {
                // 1 is not enough!
                Thread.sleep(10);
                // solver.interrupt();
              } catch (InterruptedException pE) {
                throw new UnsupportedOperationException("Unexpected interrupt");
              }
            });

    t.start();
    // According to the API of CVC5 this should either throw a UnsafeInterruptedException if the
    // solver is running or ModalException if the solver is not running. But it does not, it
    // returns the input, but not in a way that its equal to the input.
    Term result = solver.getQuantifierElimination(assertion);
    String resultString =
        "(forall ((x_b Int)) (let ((_let_0 (select a x_b))) (or (= _let_0 0) (= _let_0 1))) )";
    assertThat(result.toString()).isEqualTo(resultString);
  }

  /** CVC5 does not support Bv quantifier elim. This is expected to fail! */
  @Test
  public void checkQuantifierEliminationBV() throws CVC5ApiException {
    // build formula: exists y : bv[2]. x * y = 1
    // quantifier-free equivalent: x = 1 | x = 3
    // or extract_0_0 x = 1

    int width = 2;

    Term xBv = solver.mkConst(solver.mkBitVectorSort(width), "x_bv");
    Term yBv = solver.mkConst(solver.mkBitVectorSort(width), "y_bv");
    Term body =
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.MULT, xBv, yBv), solver.mkBitVector(1));

    Term xBound = solver.mkVar(solver.mkBitVectorSort(width), "y_bv");
    Term quantifiedVars = solver.mkTerm(Kind.VARIABLE_LIST, xBound);
    Term bodySubst = body.substitute(yBv, xBound);
    Term assertion = solver.mkTerm(Kind.EXISTS, quantifiedVars, bodySubst);

    assertThrows(RuntimeException.class, () -> solver.getQuantifierElimination(assertion));
  }

  @Test
  public void checkArraySat() {
    // ((x = 123) & (select(arr, 5) = 123)) => ((select(arr, 5) = x) & (x = 123))
    Term five = solver.mkInteger(5);
    Term oneTwoThree = solver.mkInteger(123);

    Term xInt = solver.mkVar(solver.getIntegerSort(), "x_int");

    Sort arraySort = solver.mkArraySort(solver.getIntegerSort(), solver.getIntegerSort());
    Term arr = solver.mkVar(arraySort, "arr");

    Term xEq123 = solver.mkTerm(Kind.EQUAL, xInt, oneTwoThree);
    Term selAat5Eq123 =
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.SELECT, arr, five), oneTwoThree);
    Term selAat5EqX = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.SELECT, arr, five), xInt);

    Term leftAnd = solver.mkTerm(Kind.AND, xEq123, selAat5Eq123);
    Term rightAnd = solver.mkTerm(Kind.AND, xEq123, selAat5EqX);
    Term impl = solver.mkTerm(Kind.IMPLIES, leftAnd, rightAnd);

    solver.assertFormula(impl);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkArrayUnsat() {
    // (x = 123) & (select(arr, 5) = 123) & (select(arr, 5) != x)
    Term five = solver.mkInteger(5);
    Term oneTwoThree = solver.mkInteger(123);

    Term xInt = solver.mkVar(solver.getIntegerSort(), "x_int");

    Sort arraySort = solver.mkArraySort(solver.getIntegerSort(), solver.getIntegerSort());
    Term arr = solver.mkVar(arraySort, "arr");

    Term xEq123 = solver.mkTerm(Kind.EQUAL, xInt, oneTwoThree);
    Term selAat5Eq123 =
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.SELECT, arr, five), oneTwoThree);
    Term selAat5NotEqX =
        solver.mkTerm(
            Kind.NOT, solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.SELECT, arr, five), xInt));

    Term assertion = solver.mkTerm(Kind.AND, xEq123, selAat5Eq123, selAat5NotEqX);

    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkUnsatCore() {
    // (a & b) & (not(a OR b))
    // Enable UNSAT Core first!
    solver.setOption("produce-unsat-cores", "true");

    Sort boolSort = solver.getBooleanSort();
    Term a = solver.mkVar(boolSort, "a");
    Term b = solver.mkVar(boolSort, "b");

    Term aAndb = solver.mkTerm(Kind.AND, a, b);
    Term notaOrb = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.OR, a, b));

    solver.assertFormula(aAndb);
    solver.assertFormula(notaOrb);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();

    Term[] unsatCore = solver.getUnsatCore();

    // UnsatCores are iterable
    for (Term e : unsatCore) {
      assertThat(e.toString()).isIn(Arrays.asList("(not (or a b))", "(and a b)"));
    }
  }

  @Test
  public void checkCustomTypesAndUFs() {
    // 0 <= f(x)
    // 0 <= f(y)
    // f(x) + f(y) <= 1
    // not p(0)
    // p(f(y))
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);

    Sort boolSort = solver.getBooleanSort();
    Sort intSort = solver.getIntegerSort();

    // You may use custom sorts just like bool or int
    Sort mySort = solver.mkParamSort("f");
    // Sort for UFs later
    Sort mySortToInt = solver.mkFunctionSort(mySort, intSort);
    Sort intToBool = solver.mkFunctionSort(intSort, boolSort);

    Term xTyped = solver.mkVar(mySort, "x");
    Term yTyped = solver.mkVar(mySort, "y");

    // declare UFs
    Term f = solver.mkConst(mySortToInt, "f");
    Term p = solver.mkConst(intToBool, "p");

    // Apply UFs
    Term fx = solver.mkTerm(Kind.APPLY_UF, f, xTyped);
    Term fy = solver.mkTerm(Kind.APPLY_UF, f, yTyped);
    Term sum = solver.mkTerm(Kind.PLUS, fx, fy);
    Term p0 = solver.mkTerm(Kind.APPLY_UF, p, zero);
    Term pfy = solver.mkTerm(Kind.APPLY_UF, p, fy);

    // Make some assumptions
    Term assumptions1 =
        solver.mkTerm(
            Kind.AND,
            solver.mkTerm(Kind.LEQ, zero, fx),
            solver.mkTerm(Kind.LEQ, zero, fy),
            solver.mkTerm(Kind.LEQ, sum, one));

    Term assumptions2 = solver.mkTerm(Kind.AND, p0.notTerm(), pfy);

    solver.assertFormula(assumptions1);
    solver.assertFormula(assumptions2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkBooleanUFDeclaration() {
    Sort boolSort = solver.getBooleanSort();
    Sort intSort = solver.getIntegerSort();

    // arg is bool, return is int
    Sort ufSort = solver.mkFunctionSort(boolSort, intSort);
    Term uf = solver.mkConst(ufSort, "fun_bi");
    Term ufTrue = solver.mkTerm(Kind.APPLY_UF, uf, solver.mkTrue());
    Term ufFalse = solver.mkTerm(Kind.APPLY_UF, uf, solver.mkFalse());

    Term assumptions = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, ufTrue, ufFalse));

    solver.assertFormula(assumptions);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkLIAUfsUnsat() {
    // 0 <= f(x)
    // 0 <= f(y)
    // f(x) + f(y) = x
    // f(x) + f(y) = y
    // f(x) = x + 1
    // f(y) = y - 1
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);

    Sort intSort = solver.getIntegerSort();

    // Sort for UFs later
    Sort intToInt = solver.mkFunctionSort(intSort, intSort);

    Term xInt = solver.mkConst(intSort, "x");
    Term yInt = solver.mkConst(intSort, "y");

    // declare UFs
    Term f = solver.mkConst(intToInt, "f");

    // Apply UFs
    Term fx = solver.mkTerm(Kind.APPLY_UF, f, xInt);
    Term fy = solver.mkTerm(Kind.APPLY_UF, f, yInt);
    Term plus = solver.mkTerm(Kind.PLUS, fx, fy);

    // Make some assumptions
    Term assumptions1 =
        solver.mkTerm(
            Kind.AND,
            solver.mkTerm(Kind.LEQ, zero, fx),
            solver.mkTerm(Kind.EQUAL, plus, xInt),
            solver.mkTerm(Kind.LEQ, zero, fy));

    Term assumptions2 =
        solver.mkTerm(
            Kind.AND,
            solver.mkTerm(Kind.EQUAL, fx, solver.mkTerm(Kind.PLUS, xInt, one)),
            solver.mkTerm(Kind.EQUAL, fy, solver.mkTerm(Kind.MINUS, yInt, one)),
            solver.mkTerm(Kind.EQUAL, plus, yInt));

    solver.assertFormula(assumptions1);
    solver.assertFormula(assumptions2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkLIAUfsSat() {
    // f(x) = x + 1
    // f(y) = y - 1
    // x = y -> f(x) + f(y) = x AND f(x) + f(y) = y
    Term one = solver.mkInteger(1);

    Sort intSort = solver.getIntegerSort();

    // Sort for UFs later
    Sort intToInt = solver.mkFunctionSort(intSort, intSort);

    Term xInt = solver.mkConst(intSort, "x");
    Term yInt = solver.mkConst(intSort, "y");

    // declare UFs
    Term f = solver.mkConst(intToInt, "f");

    // Apply UFs
    Term fx = solver.mkTerm(Kind.APPLY_UF, f, xInt);
    Term fy = solver.mkTerm(Kind.APPLY_UF, f, yInt);
    Term plus = solver.mkTerm(Kind.PLUS, fx, fy);

    Term plusEqx = solver.mkTerm(Kind.EQUAL, plus, xInt);
    Term plusEqy = solver.mkTerm(Kind.EQUAL, plus, yInt);
    Term xEqy = solver.mkTerm(Kind.EQUAL, yInt, xInt);
    Term xEqyImplplusEqxAndy =
        solver.mkTerm(Kind.IMPLIES, xEqy, solver.mkTerm(Kind.AND, plusEqx, plusEqy));

    Term assumptions =
        solver.mkTerm(
            Kind.AND,
            solver.mkTerm(Kind.EQUAL, fx, solver.mkTerm(Kind.PLUS, xInt, one)),
            solver.mkTerm(Kind.EQUAL, fy, solver.mkTerm(Kind.MINUS, yInt, one)),
            xEqyImplplusEqxAndy);

    solver.assertFormula(assumptions);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Sets up array and quantifier based formulas for tests. */
  public void setupArrayQuant() {
    Term zero = solver.mkInteger(0);
    Term one = solver.mkInteger(1);

    x = solver.mkVar(solver.getIntegerSort(), "x");

    Sort arraySort = solver.mkArraySort(solver.getIntegerSort(), solver.getIntegerSort());
    array = solver.mkVar(arraySort, "a");

    aAtxEq0 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.SELECT, array, x), zero);
    aAtxEq1 = solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.SELECT, array, x), one);
  }

  /**
   * For some reason CVC5 does not provide API to create max (or min) size signed/unsiged
   * bitvectors.
   *
   * @param width of the bitvector term.
   * @param signed true if signed. false for unsigned.
   * @return Max size bitvector term.
   */
  public Term makeMaxCVC5Bitvector(int width, boolean signed) throws CVC5ApiException {
    String bitvecString;
    if (signed) {
      bitvecString = new String(new char[width - 1]).replace("\0", "1");
      bitvecString = "0" + bitvecString;
    } else {
      bitvecString = new String(new char[width]).replace("\0", "1");
    }
    return solver.mkBitVector(width, bitvecString, 2);
  }
}
