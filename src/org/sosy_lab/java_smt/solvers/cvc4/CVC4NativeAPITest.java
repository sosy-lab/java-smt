// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import edu.stanford.CVC4.ArrayType;
import edu.stanford.CVC4.BitVector;
import edu.stanford.CVC4.BitVectorType;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.FloatingPoint;
import edu.stanford.CVC4.FloatingPointSize;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.Result;
import edu.stanford.CVC4.Result.Sat;
import edu.stanford.CVC4.RoundingMode;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.SortType;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.UnsatCore;
import edu.stanford.CVC4.vectorExpr;
import java.io.FileNotFoundException;
import java.io.UnsupportedEncodingException;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

/*
 * Please note that CVC4 does not have a native variable cache!
 * Each variable created is a new one with a new internal id, even if they are named the same.
 * As a result, checking equality on 2 formulas that are build with new variables
 *  that are named the same results in false!
 * Additionally, CVC4 only supports quantifier elimination for LIA and LRA.
 * However, it might run endlessly in some cases if you try quantifier elimination on array
 * theories!
 */
public class CVC4NativeAPITest {

  private static final String INVALID_GETVALUE_STRING =
      "Cannot get-value unless immediately preceded by SAT/NOT_ENTAILED or UNKNOWN response.";

  private static final String INVALID_MODEL_STRING =
      "Cannot get model unless immediately preceded by SAT/NOT_ENTAILED or UNKNOWN response.";

  private Expr x;
  private Expr array;
  private Expr aAtxEq0;
  private Expr aAtxEq1;

  @BeforeClass
  public static void loadCVC4() {
    try {
      NativeLibraries.loadLibrary("cvc4jni");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("CVC4 is not available", e);
    }
  }

  private ExprManager exprMgr;
  private SmtEngine smtEngine;

  @Before
  public void createEnvironment() {
    exprMgr = new ExprManager();
    smtEngine = new SmtEngine(exprMgr);
    // Set the logic
    smtEngine.setLogic("ALL");

    // options
    smtEngine.setOption("produce-models", new SExpr(true));
    smtEngine.setOption("finite-model-find", new SExpr(true));
    smtEngine.setOption("sets-ext", new SExpr(true));
    smtEngine.setOption("output-language", new SExpr("smt2"));
  }

  @After
  public void freeEnvironment() {
    smtEngine.delete();
    exprMgr.delete();
  }

  @Test
  public void checkSimpleUnsat() {
    smtEngine.assertFormula(exprMgr.mkConst(false));
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleSat() {
    smtEngine.assertFormula(exprMgr.mkConst(true));
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleEqualitySat() {
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, one, one);
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleEqualityUnsat() {
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, zero, one);
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleInequalityUnsat() {
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr assertion = exprMgr.mkExpr(Kind.NOT, exprMgr.mkExpr(Kind.EQUAL, one, one));
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleInequalitySat() {
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr assertion = exprMgr.mkExpr(Kind.NOT, exprMgr.mkExpr(Kind.EQUAL, zero, one));
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleLIAEqualitySat() {
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr two = exprMgr.mkConst(new Rational(2));
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, one, one), two);
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleLIAEqualityUnsat() {
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, one, one), one);
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleLIASat() {
    // x + y = 4 AND x * y = 4
    Expr four = exprMgr.mkConst(new Rational(4));
    Expr varX = exprMgr.mkVar("x", exprMgr.integerType());
    Expr varY = exprMgr.mkVar("y", exprMgr.integerType());
    Expr assertion1 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.MULT, varX, varY), four);
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, varX, varY), four);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
    assertThat(getInt(varX) + getInt(varY)).isEqualTo(4);
    assertThat(getInt(varX) * getInt(varY)).isEqualTo(4);
  }

  /** Helper to get to int values faster. */
  private int getInt(Expr cvc4Expr) {
    String string = smtEngine.getValue(cvc4Expr).toString();
    return Integer.parseInt(string);
  }

  @Test
  public void checkSimpleLIAUnsat() {
    // x + y = 1 AND x * y = 1
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr varX = exprMgr.mkVar("x", exprMgr.integerType());
    Expr varY = exprMgr.mkVar("y", exprMgr.integerType());
    Expr assertion1 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.MULT, varX, varY), one);
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, varX, varY), one);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkLIAModel() {
    // 1 + 2 = var
    // it follows that var = 3
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr two = exprMgr.mkConst(new Rational(2));
    Expr var = exprMgr.mkVar(exprMgr.integerType());
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, one, two), var);
    Result result = smtEngine.checkSat(assertion);
    assertThat(result.isSat()).isEqualTo(Sat.SAT);
    Expr assertionValue = smtEngine.getValue(assertion);
    assertThat(assertionValue.toString()).isEqualTo("true");
    assertThat(smtEngine.getValue(var).toString()).isEqualTo("3");
  }

  @Test
  public void checkSimpleLIRAUnsat2() {
    // x + y = 4 AND x * y = 4
    Expr threeHalf = exprMgr.mkConst(new Rational(3, 2));
    Expr varX = exprMgr.mkVar("x", exprMgr.integerType());
    Expr varY = exprMgr.mkVar("y", exprMgr.realType());
    Expr assertion1 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.MULT, varX, varY), threeHalf);
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, varX, varY), threeHalf);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleLIRASat() {
    // x + y = 8/5 AND x > 0 AND y > 0 AND x < 8/5 AND y < 8/5
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr eightFifth = exprMgr.mkConst(new Rational(8, 5));
    Expr varX = exprMgr.mkVar("x", exprMgr.realType());
    Expr varY = exprMgr.mkVar("y", exprMgr.integerType());
    Expr assertion1 = exprMgr.mkExpr(Kind.GT, varX, zero);
    Expr assertion2 = exprMgr.mkExpr(Kind.GT, varY, zero);
    Expr assertion3 = exprMgr.mkExpr(Kind.LT, varX, eightFifth);
    Expr assertion4 = exprMgr.mkExpr(Kind.LT, varY, eightFifth);
    Expr assertion5 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, varX, varY), eightFifth);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    smtEngine.assertFormula(assertion3);
    smtEngine.assertFormula(assertion4);
    smtEngine.assertFormula(assertion5);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleLRASat() {
    // x * y = 8/5 AND x < 4/5
    Expr fourFifth = exprMgr.mkConst(new Rational(4, 5));
    Expr eightFifth = exprMgr.mkConst(new Rational(8, 5));
    Expr varX = exprMgr.mkVar("x", exprMgr.realType());
    Expr varY = exprMgr.mkVar("y", exprMgr.realType());

    Expr assertion1 =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.NONLINEAR_MULT, varX, varY), eightFifth);
    Expr assertion2 = exprMgr.mkExpr(Kind.LT, varX, fourFifth);

    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  /** Exponents may only be natural number constants. */
  @Test
  public void checkSimplePow() {
    // x ^ 2 = 4 AND x ^ 3 = 8
    Expr two = exprMgr.mkConst(new Rational(2));
    Expr three = exprMgr.mkConst(new Rational(3));
    Expr four = exprMgr.mkConst(new Rational(4));
    Expr eight = exprMgr.mkConst(new Rational(8));
    Expr varX = exprMgr.mkVar("x", exprMgr.realType());
    Expr assertion1 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.POW, varX, two), four);
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.POW, varX, three), eight);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  /**
   * Do not ever try to use decimals in a new Rational that has only a 0 as decimal. This will
   * SIGSEV CVC4!
   */
  @Test
  public void checkSimpleFPSat() {
    // x * y = 1/4
    RoundingMode rm = RoundingMode.roundNearestTiesToAway;
    Expr rmExpr = exprMgr.mkConst(rm);
    Expr oneFourth =
        exprMgr.mkConst(new FloatingPoint(new FloatingPointSize(8, 24), rm, new Rational(1, 4)));

    Expr varX = exprMgr.mkVar("x", exprMgr.mkFloatingPointType(8, 24));
    Expr varY = exprMgr.mkVar("y", exprMgr.mkFloatingPointType(8, 24));
    Expr assertion1 =
        exprMgr.mkExpr(
            Kind.FLOATINGPOINT_EQ,
            exprMgr.mkExpr(Kind.FLOATINGPOINT_MULT, rmExpr, varX, varY),
            oneFourth);

    smtEngine.assertFormula(assertion1);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleFPUnsat() {
    // x * y = 1/4 AND x > 0 AND y < 0
    RoundingMode rm = RoundingMode.roundNearestTiesToAway;
    Expr rmExpr = exprMgr.mkConst(rm);
    Expr oneFourth =
        exprMgr.mkConst(new FloatingPoint(new FloatingPointSize(8, 24), rm, new Rational(1, 4)));

    Expr zero =
        exprMgr.mkConst(
            new FloatingPoint(
                new FloatingPointSize(8, 24),
                RoundingMode.roundNearestTiesToAway,
                new Rational(0)));

    Expr varX = exprMgr.mkVar("x", exprMgr.mkFloatingPointType(8, 24));
    Expr varY = exprMgr.mkVar("y", exprMgr.mkFloatingPointType(8, 24));
    Expr assertion1 =
        exprMgr.mkExpr(
            Kind.FLOATINGPOINT_EQ,
            exprMgr.mkExpr(Kind.FLOATINGPOINT_MULT, rmExpr, varX, varY),
            oneFourth);
    Expr assertion2 = exprMgr.mkExpr(Kind.FLOATINGPOINT_GT, varX, zero);
    Expr assertion3 = exprMgr.mkExpr(Kind.FLOATINGPOINT_LT, varY, zero);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    smtEngine.assertFormula(assertion3);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleLRAUnsat() {
    // x + y = x * y AND x - 1 = 0
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr varX = exprMgr.mkVar("x", exprMgr.realType());
    Expr varY = exprMgr.mkVar("y", exprMgr.realType());
    Expr assertion1 =
        exprMgr.mkExpr(
            Kind.EQUAL,
            exprMgr.mkExpr(Kind.NONLINEAR_MULT, varX, varY),
            exprMgr.mkExpr(Kind.PLUS, varX, varY));
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.MINUS, varX, one), zero);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleLRAUnsat2() {
    // x + y = 3/2 AND x * y = 3/2
    Expr threeHalf = exprMgr.mkConst(new Rational(3, 2));
    Expr varX = exprMgr.mkVar("x", exprMgr.realType());
    Expr varY = exprMgr.mkVar("y", exprMgr.realType());
    Expr assertion1 =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.NONLINEAR_MULT, varX, varY), threeHalf);
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, varX, varY), threeHalf);
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleIncrementalSolving() {
    // x + y = 3/2 AND x * y = 3/2 (AND x - 1 = 0)
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));
    Expr threeHalf = exprMgr.mkConst(new Rational(3, 2));
    Expr varX = exprMgr.mkVar("x", exprMgr.realType());
    Expr varY = exprMgr.mkVar("y", exprMgr.realType());
    // this alone is SAT
    Expr assertion1 =
        exprMgr.mkExpr(
            Kind.EQUAL,
            exprMgr.mkExpr(Kind.NONLINEAR_MULT, varX, varY),
            exprMgr.mkExpr(Kind.PLUS, varX, varY));
    // both 2 and 3 make it UNSAT (either one)
    Expr assertion2 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.PLUS, varX, varY), threeHalf);
    Expr assertion3 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.MINUS, varX, one), zero);
    smtEngine.push();
    smtEngine.assertFormula(assertion1);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
    smtEngine.push();
    smtEngine.assertFormula(assertion2);
    satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
    smtEngine.pop();
    satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
    smtEngine.push();
    smtEngine.assertFormula(assertion3);
    satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
    smtEngine.pop();
    satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  /** Note that model and getValue are seperate! */
  @Test
  public void checkInvalidModelGetValue() {
    Expr assertion = exprMgr.mkConst(false);
    Result result = smtEngine.checkSat(assertion);
    assertThat(result.isSat()).isEqualTo(Sat.UNSAT);
    Exception e =
        assertThrows(edu.stanford.CVC4.Exception.class, () -> smtEngine.getValue(assertion));
    assertThat(e.toString()).contains(INVALID_GETVALUE_STRING);
  }

  /** For reasons unknown you can get a model, but you can't do anything with it. */
  @Test
  public void checkInvalidModel() {
    Result result = smtEngine.checkSat(exprMgr.mkConst(false));
    assertThat(result.isSat()).isEqualTo(Sat.UNSAT);
    Exception e = assertThrows(edu.stanford.CVC4.Exception.class, () -> smtEngine.getModel());
    assertThat(e.toString()).contains(INVALID_MODEL_STRING);
  }

  /** It does not matter if you take an int or array or bv here, all result in the same error. */
  @Test
  public void checkInvalidTypeOperationsAssert() {
    BitVectorType bvType = exprMgr.mkBitVectorType(16);
    Expr bvVar = exprMgr.mkVar("bla", bvType);
    Expr assertion = exprMgr.mkExpr(Kind.AND, bvVar, bvVar);

    Exception e =
        assertThrows(edu.stanford.CVC4.Exception.class, () -> smtEngine.assertFormula(assertion));
    assertThat(e.toString()).contains("expecting a Boolean subexpression");
  }

  /** It does not matter if you take an int or array or bv here, all result in the same error. */
  @Test
  public void checkInvalidTypeOperationsCheckSat() {
    BitVectorType bvType = exprMgr.mkBitVectorType(16);
    Expr bvVar = exprMgr.mkVar("bla", bvType);
    Expr assertion = exprMgr.mkExpr(Kind.AND, bvVar, bvVar);

    Exception e =
        assertThrows(edu.stanford.CVC4.Exception.class, () -> smtEngine.checkSat(assertion));
    assertThat(e.toString()).contains("expecting a Boolean subexpression");
  }

  @Test
  public void checkBvInvalidWidthAssertion() {
    Expr bvOne = exprMgr.mkConst(new BitVector(0, 1));
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, bvOne, bvOne);

    Exception e =
        assertThrows(edu.stanford.CVC4.Exception.class, () -> smtEngine.assertFormula(assertion));
    assertThat(e.toString()).contains("constant of size 0");
  }

  @Test
  public void checkBvInvalidWidthCheckSat() {
    Expr bvOne = exprMgr.mkConst(new BitVector(0, 1));
    Expr assertion = exprMgr.mkExpr(Kind.EQUAL, bvOne, bvOne);

    Exception e =
        assertThrows(edu.stanford.CVC4.Exception.class, () -> smtEngine.checkSat(assertion));
    assertThat(e.toString()).contains("constant of size 0");
  }

  @Test
  public void checkSimpleBvEqualitySat() {
    // 1 + 0 = 1 with bitvectors
    Expr bvOne = exprMgr.mkConst(new BitVector(16, 1));
    Expr bvZero = exprMgr.mkConst(new BitVector(16, 0));
    Expr assertion =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.BITVECTOR_PLUS, bvZero, bvOne), bvOne);
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkSimpleBvEqualityUnsat() {
    // 0 + 1 = 2 UNSAT with bitvectors
    Expr bvZero = exprMgr.mkConst(new BitVector(16, 0));
    Expr bvOne = exprMgr.mkConst(new BitVector(16, 1));
    Expr bvTwo = exprMgr.mkConst(new BitVector(16, 2));
    Expr assertion =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.BITVECTOR_PLUS, bvZero, bvOne), bvTwo);
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkSimpleBvUnsat() {
    // var + 1 = 0 & var < max bitvector & var > 0; both < and > signed
    // Because of bitvector nature its UNSAT now
    Expr bvVar = exprMgr.mkBoundVar(exprMgr.mkBitVectorType(16));
    Expr bvOne = exprMgr.mkConst(new BitVector(16, 1));
    Expr bvZero = exprMgr.mkConst(new BitVector(16, 0));
    Expr assertion1 =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.BITVECTOR_PLUS, bvVar, bvOne), bvZero);
    Expr assertion2 =
        exprMgr.mkExpr(Kind.BITVECTOR_SLT, bvVar, exprMgr.mkConst(BitVector.mkMaxSigned(16)));
    Expr assertion3 =
        exprMgr.mkExpr(Kind.BITVECTOR_SGT, bvVar, exprMgr.mkConst(new BitVector(16, 0)));
    smtEngine.assertFormula(assertion1);
    smtEngine.assertFormula(assertion2);
    smtEngine.assertFormula(assertion3);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  /*
   * CVC4 fails some easy quantifier tests. To check wheter or not they really fail in CVC4 or due
   * to JavaSMT we test them in the native API.
   */
  @Test
  public void checkQuantifierExistsIncomplete() {
    // (not exists x . not b[x] = 0) AND (b[123] = 0) is SAT

    setupArrayQuant();
    Expr zero = exprMgr.mkConst(new Rational(0));

    Expr xBound = exprMgr.mkBoundVar("x", exprMgr.integerType());
    vectorExpr vec = new vectorExpr();
    vec.add(xBound);
    Expr quantifiedVars = exprMgr.mkExpr(Kind.BOUND_VAR_LIST, vec);
    Expr aAtxEq0s = aAtxEq0.substitute(x, xBound);
    Expr exists = exprMgr.mkExpr(Kind.EXISTS, quantifiedVars, exprMgr.mkExpr(Kind.NOT, aAtxEq0s));
    Expr notExists = exprMgr.mkExpr(Kind.NOT, exists);

    Expr select123 = exprMgr.mkExpr(Kind.SELECT, array, exprMgr.mkConst(new Rational(123)));
    Expr selectEq0 = exprMgr.mkExpr(Kind.EQUAL, select123, zero);
    Expr assertion = exprMgr.mkExpr(Kind.AND, notExists, selectEq0);

    // assertFormula has a return value, check?
    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    // CVC4 fails this test as incomplete
    assertThat(satCheck.isUnknown()).isTrue();
    assertThat(satCheck.whyUnknown()).isEqualTo(Result.UnknownExplanation.INCOMPLETE);
  }

  @Test
  public void checkQuantifierEliminationLIA() {
    // build formula: (forall x . ((x < 5) | (7 < x + y)))
    // quantifier-free equivalent: (2 < y) or (>= y 3)
    setupArrayQuant();

    Expr three = exprMgr.mkConst(new Rational(3));
    Expr five = exprMgr.mkConst(new Rational(5));
    Expr seven = exprMgr.mkConst(new Rational(7));

    Expr y = exprMgr.mkVar("y", exprMgr.integerType());

    Expr first = exprMgr.mkExpr(Kind.LT, x, five);
    Expr second = exprMgr.mkExpr(Kind.LT, seven, exprMgr.mkExpr(Kind.PLUS, x, y));
    Expr body = exprMgr.mkExpr(Kind.OR, first, second);

    Expr xBound = exprMgr.mkBoundVar("x", exprMgr.integerType());
    vectorExpr vec = new vectorExpr();
    vec.add(xBound);
    Expr quantifiedVars = exprMgr.mkExpr(Kind.BOUND_VAR_LIST, vec);
    Expr bodySubst = body.substitute(x, xBound);
    Expr assertion = exprMgr.mkExpr(Kind.FORALL, quantifiedVars, bodySubst);

    Expr result = smtEngine.doQuantifierElimination(assertion, true);

    Expr resultCheck = exprMgr.mkExpr(Kind.GEQ, y, three);
    assertThat(result.toString()).isEqualTo(resultCheck.toString());
  }

  @SuppressWarnings("unused")
  @Test
  public void checkQuantifierWithUf() throws FileNotFoundException, UnsupportedEncodingException {
    Expr var = exprMgr.mkVar("var", exprMgr.integerType());
    // start with a normal, free variable!
    Expr boundVar = exprMgr.mkVar("boundVar", exprMgr.integerType());
    Expr varIsOne = exprMgr.mkExpr(Kind.EQUAL, var, exprMgr.mkConst(new Rational(1)));
    // try not to use 0 as this is the default value for CVC4 models
    Expr boundVarIsTwo = exprMgr.mkExpr(Kind.EQUAL, boundVar, exprMgr.mkConst(new Rational(2)));
    Expr boundVarIsOne = exprMgr.mkExpr(Kind.EQUAL, boundVar, exprMgr.mkConst(new Rational(1)));

    String func = "func";
    Type intType = exprMgr.integerType();

    Type ufType = exprMgr.mkFunctionType(intType, intType);
    Expr uf = exprMgr.mkVar(func, ufType);
    Expr funcAtBoundVar = exprMgr.mkExpr(uf, boundVar);

    Expr body =
        exprMgr.mkExpr(Kind.AND, boundVarIsTwo, exprMgr.mkExpr(Kind.EQUAL, var, funcAtBoundVar));

    // This is the bound variable used for boundVar
    Expr boundVarBound = exprMgr.mkBoundVar("boundVar", exprMgr.integerType());
    vectorExpr vec = new vectorExpr();
    vec.add(boundVarBound);
    Expr quantifiedVars = exprMgr.mkExpr(Kind.BOUND_VAR_LIST, vec);
    // Subst all boundVar variables with the bound version
    Expr bodySubst = body.substitute(boundVar, boundVarBound);
    Expr quantFormula = exprMgr.mkExpr(Kind.EXISTS, quantifiedVars, bodySubst);

    // var = 1 & boundVar = 1 & exists boundVar . ( boundVar = 2 & f(boundVar) = var )
    Expr overallFormula = exprMgr.mkExpr(Kind.AND, varIsOne, boundVarIsOne, quantFormula);

    smtEngine.assertFormula(overallFormula);

    Result satCheck = smtEngine.checkSat();

    // SAT
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);

    // check Model
    // var = 1 & boundVar = 1 & exists boundVar . ( boundVar = 2 & f(2) = 1 )
    // It seems like CVC4 can't return quantified variables,
    // therefore we can't get a value for the uf!
    assertThat(smtEngine.getValue(var).toString()).isEqualTo("1");
    assertThat(smtEngine.getValue(boundVar).toString()).isEqualTo("1");

    assertThat(smtEngine.getValue(funcAtBoundVar).toString()).isEqualTo("1");
    assertThat(smtEngine.getValue(boundVarBound).toString()).isEqualTo("boundVar");
  }

  /**
   * CVC4 does not support Array quantifier elimination. This is expected to fail! But it runs
   * endlessly. So we can check interruption on it.
   */
  @Test
  public void checkInterruptBehaviour() {
    setupArrayQuant();
    Expr body = exprMgr.mkExpr(Kind.OR, aAtxEq0, aAtxEq1);

    Expr xBound = exprMgr.mkBoundVar("x_b", exprMgr.integerType());
    vectorExpr vec = new vectorExpr();
    vec.add(xBound);
    Expr quantifiedVars = exprMgr.mkExpr(Kind.BOUND_VAR_LIST, vec);
    Expr bodySubst = body.substitute(x, xBound);
    Expr assertion = exprMgr.mkExpr(Kind.FORALL, quantifiedVars, bodySubst);

    Thread t =
        new Thread(
            () -> {
              try {
                // 1 is not enough!
                Thread.sleep(10);
                smtEngine.interrupt();
              } catch (InterruptedException exception) {
                throw new UnsupportedOperationException("Unexpected interrupt", exception);
              }
            });

    t.start();
    // According to the API of CVC4 this should either throw a UnsafeInterruptedException if the
    // SMTEngine is running or ModalException if the SMTEngine is not running. But it does not, it
    // returns the input, but not in a way that its equal to the input.
    Expr result = smtEngine.doQuantifierElimination(assertion, true);
    String resultString =
        "(forall ((x_b Int)) (let ((_let_0 (select a x_b))) (or (= _let_0 0) (= _let_0 1))) )";
    assertThat(result.toString()).isEqualTo(resultString);
  }

  /** CVC4 does not support Bv quantifier elim. This is expected to fail! */
  @Test
  public void checkQuantifierEliminationBV() {
    // build formula: exists y : bv[2]. x * y = 1
    // quantifier-free equivalent: x = 1 | x = 3
    // or extract_0_0 x = 1

    int width = 2;

    Expr xBv = exprMgr.mkVar("x_bv", exprMgr.mkBitVectorType(width));
    Expr yBv = exprMgr.mkVar("y_bv", exprMgr.mkBitVectorType(width));
    Expr body =
        exprMgr.mkExpr(
            Kind.EQUAL, exprMgr.mkExpr(Kind.MULT, xBv, yBv), exprMgr.mkConst(new BitVector(1)));

    Expr xBound = exprMgr.mkBoundVar("y_bv", exprMgr.mkBitVectorType(width));
    vectorExpr vec = new vectorExpr();
    vec.add(xBound);
    Expr quantifiedVars = exprMgr.mkExpr(Kind.BOUND_VAR_LIST, vec);
    Expr bodySubst = body.substitute(yBv, xBound);
    Expr assertion = exprMgr.mkExpr(Kind.EXISTS, quantifiedVars, bodySubst);

    assertThrows(RuntimeException.class, () -> smtEngine.doQuantifierElimination(assertion, true));
  }

  @Test
  public void checkArraySat() {
    // ((x = 123) & (select(arr, 5) = 123)) => ((select(arr, 5) = x) & (x = 123))
    Expr five = exprMgr.mkConst(new Rational(5));
    Expr oneTwoThree = exprMgr.mkConst(new Rational(123));

    Expr xInt = exprMgr.mkVar("x_int", exprMgr.integerType());

    ArrayType arrayType = exprMgr.mkArrayType(exprMgr.integerType(), exprMgr.integerType());
    Expr arr = exprMgr.mkVar("arr", arrayType);

    Expr xEq123 = exprMgr.mkExpr(Kind.EQUAL, xInt, oneTwoThree);
    Expr selAat5Eq123 =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.SELECT, arr, five), oneTwoThree);
    Expr selAat5EqX = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.SELECT, arr, five), xInt);

    Expr leftAnd = exprMgr.mkExpr(Kind.AND, xEq123, selAat5Eq123);
    Expr rightAnd = exprMgr.mkExpr(Kind.AND, xEq123, selAat5EqX);
    Expr impl = exprMgr.mkExpr(Kind.IMPLIES, leftAnd, rightAnd);

    smtEngine.assertFormula(impl);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkArrayUnsat() {
    // (x = 123) & (select(arr, 5) = 123) & (select(arr, 5) != x)
    Expr five = exprMgr.mkConst(new Rational(5));
    Expr oneTwoThree = exprMgr.mkConst(new Rational(123));

    Expr xInt = exprMgr.mkVar("x_int", exprMgr.integerType());

    ArrayType arrayType = exprMgr.mkArrayType(exprMgr.integerType(), exprMgr.integerType());
    Expr arr = exprMgr.mkVar("arr", arrayType);

    Expr xEq123 = exprMgr.mkExpr(Kind.EQUAL, xInt, oneTwoThree);
    Expr selAat5Eq123 =
        exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.SELECT, arr, five), oneTwoThree);
    Expr selAat5NotEqX =
        exprMgr.mkExpr(
            Kind.NOT, exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.SELECT, arr, five), xInt));

    Expr assertion = exprMgr.mkExpr(Kind.AND, xEq123, selAat5Eq123, selAat5NotEqX);

    smtEngine.assertFormula(assertion);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkUnsatCore() {
    // (a & b) & (not(a OR b))
    // Enable UNSAT Core first!
    smtEngine.setOption("produce-unsat-cores", new SExpr(true));
    Type boolType = exprMgr.booleanType();
    Expr a = exprMgr.mkVar("a", boolType);
    Expr b = exprMgr.mkVar("b", boolType);

    Expr aAndb = exprMgr.mkExpr(Kind.AND, a, b);
    Expr notaOrb = exprMgr.mkExpr(Kind.NOT, exprMgr.mkExpr(Kind.OR, a, b));

    smtEngine.assertFormula(aAndb);
    smtEngine.assertFormula(notaOrb);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);

    UnsatCore unsatCore = smtEngine.getUnsatCore();

    // UnsatCores are iterable
    for (Expr e : unsatCore) {
      assertThat(e.toString()).isIn(ImmutableList.of("(not (or a b))", "(and a b)"));
    }
  }

  @Test
  public void checkCustomTypesAndUFs() {
    // 0 <= f(x)
    // 0 <= f(y)
    // f(x) + f(y) <= 1
    // not p(0)
    // p(f(y))
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));

    Type boolType = exprMgr.booleanType();
    Type intType = exprMgr.integerType();

    // You may use custom sorts just like bool or int
    SortType mySort = exprMgr.mkSort("f");
    // Type for UFs later
    Type mySortToInt = exprMgr.mkFunctionType(mySort, intType);
    Type intToBool = exprMgr.mkFunctionType(intType, boolType);

    Expr xTyped = exprMgr.mkVar("x", mySort);
    Expr yTyped = exprMgr.mkVar("y", mySort);

    // declare UFs
    Expr f = exprMgr.mkVar("f", mySortToInt);
    Expr p = exprMgr.mkVar("p", intToBool);

    // Apply UFs
    Expr fx = exprMgr.mkExpr(Kind.APPLY_UF, f, xTyped);
    Expr fy = exprMgr.mkExpr(Kind.APPLY_UF, f, yTyped);
    Expr sum = exprMgr.mkExpr(Kind.PLUS, fx, fy);
    Expr p0 = exprMgr.mkExpr(Kind.APPLY_UF, p, zero);
    Expr pfy = exprMgr.mkExpr(Kind.APPLY_UF, p, fy);

    // Make some assumptions
    Expr assumptions =
        exprMgr.mkExpr(
            Kind.AND,
            exprMgr.mkExpr(Kind.LEQ, zero, fx),
            exprMgr.mkExpr(Kind.LEQ, zero, fy),
            exprMgr.mkExpr(Kind.LEQ, sum, one),
            p0.notExpr(),
            pfy);

    smtEngine.assertFormula(assumptions);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkBooleanUFDeclaration() {
    Type boolType = exprMgr.booleanType();
    Type intType = exprMgr.integerType();

    // arg is bool, return is int
    Type ufType = exprMgr.mkFunctionType(boolType, intType);
    Expr uf = exprMgr.mkVar("fun_bi", ufType);
    Expr ufTrue = exprMgr.mkExpr(uf, exprMgr.mkConst(true));
    Expr ufFalse = exprMgr.mkExpr(uf, exprMgr.mkConst(false));

    Expr assumptions = exprMgr.mkExpr(Kind.NOT, exprMgr.mkExpr(Kind.EQUAL, ufTrue, ufFalse));

    smtEngine.assertFormula(assumptions);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  @Test
  public void checkLIAUfsUnsat() {
    // 0 <= f(x)
    // 0 <= f(y)
    // f(x) + f(y) = x
    // f(x) + f(y) = y
    // f(x) = x + 1
    // f(y) = y - 1
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));

    Type intType = exprMgr.integerType();

    // Type for UFs later
    Type intToInt = exprMgr.mkFunctionType(intType, intType);

    Expr xInt = exprMgr.mkVar("x", intType);
    Expr yInt = exprMgr.mkVar("y", intType);

    // declare UFs
    Expr f = exprMgr.mkVar("f", intToInt);

    // Apply UFs
    Expr fx = exprMgr.mkExpr(Kind.APPLY_UF, f, xInt);
    Expr fy = exprMgr.mkExpr(Kind.APPLY_UF, f, yInt);
    Expr plus = exprMgr.mkExpr(Kind.PLUS, fx, fy);

    // Make some assumptions
    Expr assumptions1 =
        exprMgr.mkExpr(
            Kind.AND, exprMgr.mkExpr(Kind.LEQ, zero, fx), exprMgr.mkExpr(Kind.LEQ, zero, fy));

    Expr assumptions2 =
        exprMgr.mkExpr(
            Kind.AND,
            exprMgr.mkExpr(Kind.EQUAL, fx, exprMgr.mkExpr(Kind.PLUS, xInt, one)),
            exprMgr.mkExpr(Kind.EQUAL, fy, exprMgr.mkExpr(Kind.MINUS, yInt, one)),
            exprMgr.mkExpr(Kind.EQUAL, plus, xInt),
            exprMgr.mkExpr(Kind.EQUAL, plus, yInt));

    smtEngine.assertFormula(assumptions1);
    smtEngine.assertFormula(assumptions2);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.UNSAT);
  }

  @Test
  public void checkLIAUfsSat() {
    // f(x) = x + 1
    // f(y) = y - 1
    // x = y -> f(x) + f(y) = x AND f(x) + f(y) = y
    Expr one = exprMgr.mkConst(new Rational(1));

    Type intType = exprMgr.integerType();

    // Type for UFs later
    Type intToInt = exprMgr.mkFunctionType(intType, intType);

    Expr xInt = exprMgr.mkVar("x", intType);
    Expr yInt = exprMgr.mkVar("y", intType);

    // declare UFs
    Expr f = exprMgr.mkVar("f", intToInt);

    // Apply UFs
    Expr fx = exprMgr.mkExpr(Kind.APPLY_UF, f, xInt);
    Expr fy = exprMgr.mkExpr(Kind.APPLY_UF, f, yInt);
    Expr plus = exprMgr.mkExpr(Kind.PLUS, fx, fy);

    Expr plusEqx = exprMgr.mkExpr(Kind.EQUAL, plus, xInt);
    Expr plusEqy = exprMgr.mkExpr(Kind.EQUAL, plus, yInt);
    Expr xEqy = exprMgr.mkExpr(Kind.EQUAL, yInt, xInt);
    Expr xEqyImplplusEqxAndy =
        exprMgr.mkExpr(Kind.IMPLIES, xEqy, exprMgr.mkExpr(Kind.AND, plusEqx, plusEqy));

    Expr assumptions =
        exprMgr.mkExpr(
            Kind.AND,
            exprMgr.mkExpr(Kind.EQUAL, fx, exprMgr.mkExpr(Kind.PLUS, xInt, one)),
            exprMgr.mkExpr(Kind.EQUAL, fy, exprMgr.mkExpr(Kind.MINUS, yInt, one)),
            xEqyImplplusEqxAndy);

    smtEngine.assertFormula(assumptions);
    Result satCheck = smtEngine.checkSat();
    assertThat(satCheck.isSat()).isEqualTo(Sat.SAT);
  }

  /** Sets up array and quantifier based formulas for tests. */
  public void setupArrayQuant() {
    Expr zero = exprMgr.mkConst(new Rational(0));
    Expr one = exprMgr.mkConst(new Rational(1));

    x = exprMgr.mkVar("x", exprMgr.integerType());

    ArrayType arrayType = exprMgr.mkArrayType(exprMgr.integerType(), exprMgr.integerType());
    array = exprMgr.mkVar("a", arrayType);

    aAtxEq0 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.SELECT, array, x), zero);
    aAtxEq1 = exprMgr.mkExpr(Kind.EQUAL, exprMgr.mkExpr(Kind.SELECT, array, x), one);
  }
}
