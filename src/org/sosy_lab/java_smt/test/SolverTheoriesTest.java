// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.junit.AssumptionViolatedException;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

@SuppressWarnings("LocalVariableName")
public class SolverTheoriesTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void basicBoolTest() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeBoolean(false);
    BooleanFormula c = bmgr.xor(a, b);
    BooleanFormula d = bmgr.makeVariable("b");
    BooleanFormula e = bmgr.xor(a, d);

    BooleanFormula notImpl = bmgr.and(a, bmgr.not(e));

    assertThatFormula(a).implies(c);
    assertThatFormula(notImpl).isSatisfiable();
  }

  @Test
  public void basicIntTest() {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    assertThat(a).isNotEqualTo(b);
  }

  @Test
  public void basisRatTest() throws SolverException, InterruptedException {
    requireRationals();

    RationalFormula a = rmgr.makeVariable("int_c");
    RationalFormula num = rmgr.makeNumber(4);

    BooleanFormula f = rmgr.equal(rmgr.add(a, a), num);
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void intTest1() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("int_a");
    IntegerFormula num = imgr.makeNumber(2);

    BooleanFormula f = imgr.equal(imgr.add(a, a), num);
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void intTest2() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("int_b");
    IntegerFormula num = imgr.makeNumber(1);

    BooleanFormula f = imgr.equal(imgr.add(a, a), num);
    assertThatFormula(f).isUnsatisfiable();
  }

  private void assertDivision(
      IntegerFormula numerator,
      IntegerFormula denominator,
      IntegerFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertDivision(true, numerator, denominator, expectedResult, constraints);
  }

  private void assertDivision(
      boolean includeNegation,
      IntegerFormula numerator,
      IntegerFormula denominator,
      IntegerFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertOperation(
        includeNegation, buildDivision(numerator, denominator, expectedResult), constraints);
  }

  private void assertDivision(
      BitvectorFormula numerator,
      BitvectorFormula denominator,
      boolean signed,
      BitvectorFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertDivision(true, numerator, denominator, signed, expectedResult, constraints);
  }

  private void assertDivision(
      boolean includeNegation,
      BitvectorFormula numerator,
      BitvectorFormula denominator,
      boolean signed,
      BitvectorFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertOperation(
        includeNegation,
        buildDivision(numerator, denominator, signed, expectedResult),
        constraints);
  }

  private void assertModulo(
      IntegerFormula numerator,
      IntegerFormula denominator,
      IntegerFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertModulo(true, numerator, denominator, expectedResult, constraints);
  }

  private void assertModulo(
      boolean includeNegation,
      IntegerFormula numerator,
      IntegerFormula denominator,
      IntegerFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertOperation(
        includeNegation, buildModulo(numerator, denominator, expectedResult), constraints);
  }

  private void assertModulo(
      BitvectorFormula numerator,
      BitvectorFormula denominator,
      boolean signed,
      BitvectorFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertModulo(true, numerator, denominator, signed, expectedResult, constraints);
  }

  private void assertModulo(
      boolean includeNegation,
      BitvectorFormula numerator,
      BitvectorFormula denominator,
      boolean signed,
      BitvectorFormula expectedResult,
      BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    assertOperation(
        includeNegation, buildModulo(numerator, denominator, signed, expectedResult), constraints);
  }

  private BooleanFormula buildDivision(
      IntegerFormula numerator, IntegerFormula denominator, IntegerFormula expectedResult) {
    return imgr.equal(imgr.divide(numerator, denominator), expectedResult);
  }

  private BooleanFormula buildDivision(
      BitvectorFormula numerator,
      BitvectorFormula denominator,
      boolean signed,
      BitvectorFormula expectedResult) {
    return bvmgr.equal(bvmgr.divide(numerator, denominator, signed), expectedResult);
  }

  private BooleanFormula buildModulo(
      IntegerFormula numerator, IntegerFormula denominator, IntegerFormula expectedResult) {
    return imgr.equal(imgr.modulo(numerator, denominator), expectedResult);
  }

  private BooleanFormula buildModulo(
      BitvectorFormula numerator,
      BitvectorFormula denominator,
      boolean signed,
      BitvectorFormula expectedResult) {
    return bvmgr.equal(bvmgr.remainder(numerator, denominator, signed), expectedResult);
  }

  private void assertOperation(
      boolean includeNegation, BooleanFormula equation, BooleanFormula... constraints)
      throws SolverException, InterruptedException {
    // check positive case
    assertThatFormula(bmgr.and(bmgr.and(constraints), equation)).isSatisfiable();

    // check negative case
    BooleanFormulaSubject negation =
        assertThatFormula(bmgr.and(bmgr.and(constraints), bmgr.not(equation)));
    if (includeNegation) {
      negation.isUnsatisfiable();
    } else {
      negation.isSatisfiable();
    }
  }

  @Test
  public void intTest3_DivModLinear() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("int_a");
    IntegerFormula b = imgr.makeVariable("int_b");

    IntegerFormula num10 = imgr.makeNumber(10);
    IntegerFormula num5 = imgr.makeNumber(5);
    IntegerFormula num3 = imgr.makeNumber(3);
    IntegerFormula num4 = imgr.makeNumber(4);
    IntegerFormula num2 = imgr.makeNumber(2);
    IntegerFormula num1 = imgr.makeNumber(1);
    IntegerFormula num0 = imgr.makeNumber(0);
    IntegerFormula numNeg2 = imgr.makeNumber(-2);
    IntegerFormula numNeg3 = imgr.makeNumber(-3);
    IntegerFormula numNeg4 = imgr.makeNumber(-4);
    IntegerFormula numNeg10 = imgr.makeNumber(-10);

    BooleanFormula aEq10 = imgr.equal(a, num10);
    BooleanFormula bEq2 = imgr.equal(b, num2);
    BooleanFormula aEqNeg10 = imgr.equal(a, numNeg10);
    BooleanFormula bEqNeg2 = imgr.equal(b, numNeg2);

    assertDivision(num10, num5, num2);
    assertDivision(num10, num3, num3);
    assertDivision(numNeg10, num5, numNeg2);
    assertDivision(numNeg10, numNeg2, num5);
    assertDivision(num10, num5, num2);
    assertDivision(num10, num3, num3);
    assertDivision(num10, numNeg3, numNeg3);
    assertDivision(num0, num3, num0);

    assertDivision(a, num5, b, aEq10, bEq2);
    assertDivision(a, num3, num3, aEq10);
    assertDivision(a, num5, b, aEqNeg10, bEqNeg2);
    assertDivision(a, num3, numNeg4, aEqNeg10);
    assertDivision(a, numNeg3, num4, aEqNeg10);

    switch (solverToUse()) {
      case MATHSAT5: // modulo not supported
        assertThrows(UnsupportedOperationException.class, () -> buildModulo(num10, num5, num0));
        break;
      default:
        assertModulo(num10, num5, num0);
        assertModulo(num10, num3, num1, aEq10);
        assertModulo(numNeg10, num5, num0);
        assertModulo(numNeg10, num3, num2);
        assertModulo(numNeg10, numNeg3, num2);

        assertModulo(a, num5, num0, aEq10);
        assertModulo(a, num3, num1, aEq10);
        assertModulo(a, num5, num0, aEqNeg10);
        assertModulo(a, num3, num2, aEqNeg10);
        assertModulo(a, numNeg3, num2, aEqNeg10);
    }
  }

  @Test
  public void intTest3_DivModLinear_zeroDenominator() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("int_a");

    IntegerFormula num10 = imgr.makeNumber(10);
    IntegerFormula num1 = imgr.makeNumber(1);
    IntegerFormula num0 = imgr.makeNumber(0);

    BooleanFormula aEq10 = imgr.equal(a, num10);

    // SMTLIB allows any value for division-by-zero.
    switch (solverToUse()) {
      case YICES2:
        assertThrows(
            IllegalArgumentException.class,
            () -> assertThatFormula(buildDivision(num10, num0, num10)).isSatisfiable());
        break;
      case OPENSMT: // INFO: OpenSMT does not allow division by zero
        assertThrows(
            UnsupportedOperationException.class,
            () -> assertThatFormula(buildDivision(num10, num0, num10)).isSatisfiable());
        break;
      default:
        // division-by-zero results in an arbitrary result
        assertDivision(false, num0, num0, num0);
        assertDivision(false, num0, num0, num1);
        assertDivision(false, num0, num0, num10);
        assertDivision(false, num10, num0, num0);
        assertDivision(false, num10, num0, num0);
        assertDivision(false, num10, num0, num10);

        assertDivision(false, a, num0, num0, aEq10);
        assertDivision(false, a, num0, num1, aEq10);
        assertDivision(false, a, num0, num10, aEq10);
    }

    switch (solverToUse()) {
      case YICES2:
        assertThrows(
            IllegalArgumentException.class,
            () -> assertThatFormula(buildModulo(num10, num0, num10)).isSatisfiable());
        break;
      case OPENSMT: // INFO
      case MATHSAT5: // modulo not supported
        assertThrows(UnsupportedOperationException.class, () -> buildModulo(num10, num0, num10));
        break;
      default:
        // modulo-by-zero results in an arbitrary result
        assertModulo(false, num0, num0, num0);
        assertModulo(false, num0, num0, num1);
        assertModulo(false, num0, num0, num10);
        assertModulo(false, num10, num0, num0);
        assertModulo(false, num10, num0, num0);
        assertModulo(false, num10, num0, num10);
        assertModulo(false, a, num0, num0, aEq10);
        assertModulo(false, a, num0, num1, aEq10);
        assertModulo(false, a, num0, num10, aEq10);
    }
  }

  @Test
  public void intTest3_DivModNonLinear() throws SolverException, InterruptedException {
    // not all solvers support division-by-variable,
    // we guarantee soundness by allowing any value that yields SAT.
    requireIntegers();

    IntegerFormula a = imgr.makeVariable("int_a");
    IntegerFormula b = imgr.makeVariable("int_b");

    IntegerFormula num10 = imgr.makeNumber(10);
    IntegerFormula num5 = imgr.makeNumber(5);
    IntegerFormula num2 = imgr.makeNumber(2);
    IntegerFormula num0 = imgr.makeNumber(0);
    IntegerFormula numNeg2 = imgr.makeNumber(-2);
    IntegerFormula numNeg10 = imgr.makeNumber(-10);

    BooleanFormula aEq10 = imgr.equal(a, num10);
    BooleanFormula bEq2 = imgr.equal(b, num2);
    BooleanFormula bEqNeg2 = imgr.equal(b, numNeg2);
    BooleanFormula aEqNeg10 = imgr.equal(a, numNeg10);

    switch (solverToUse()) {
      case OPENSMT: // INFO: OpenSmt does not allow nonlinear terms
      case SMTINTERPOL:
      case YICES2:
        assertThrows(UnsupportedOperationException.class, () -> buildDivision(a, b, num5));
        assertThrows(UnsupportedOperationException.class, () -> buildModulo(a, b, num0));
        break;
      case MATHSAT5: // modulo not supported
        assertDivision(a, b, num5, aEq10, bEq2);
        assertDivision(a, b, num5, aEqNeg10, bEqNeg2);
        assertThrows(UnsupportedOperationException.class, () -> buildModulo(num10, num5, num0));
        break;
      default:
        assertDivision(a, b, num5, aEq10, bEq2);
        assertDivision(a, b, num5, aEqNeg10, bEqNeg2);
        assertModulo(a, b, num0, aEq10, bEq2);
        assertModulo(a, b, num0, aEqNeg10, bEqNeg2);
    }

    // TODO negative case is disabled, because we would need the option
    // solver.solver.useNonLinearIntegerArithmetic=true.

  }

  @Test
  public void intTestBV_DivMod() throws SolverException, InterruptedException {
    requireBitvectors();

    final int bitsize = 8;
    BitvectorFormula a = bvmgr.makeVariable(bitsize, "int_a");
    BitvectorFormula b = bvmgr.makeVariable(bitsize, "int_b");

    BitvectorFormula num253 = bvmgr.makeBitvector(bitsize, -3); // == 253 unsigned
    BitvectorFormula num246 = bvmgr.makeBitvector(bitsize, -10); // == 246 unsigned
    BitvectorFormula num82 = bvmgr.makeBitvector(bitsize, 82);
    BitvectorFormula num49 = bvmgr.makeBitvector(bitsize, 49);
    BitvectorFormula num10 = bvmgr.makeBitvector(bitsize, 10);
    BitvectorFormula num5 = bvmgr.makeBitvector(bitsize, 5);
    BitvectorFormula num3 = bvmgr.makeBitvector(bitsize, 3);
    BitvectorFormula num2 = bvmgr.makeBitvector(bitsize, 2);
    BitvectorFormula num1 = bvmgr.makeBitvector(bitsize, 1);
    BitvectorFormula num0 = bvmgr.makeBitvector(bitsize, 0);
    BitvectorFormula numNeg1 = bvmgr.makeBitvector(bitsize, -1);
    BitvectorFormula numNeg2 = bvmgr.makeBitvector(bitsize, -2);
    BitvectorFormula numNeg3 = bvmgr.makeBitvector(bitsize, -3);
    BitvectorFormula numNeg10 = bvmgr.makeBitvector(bitsize, -10);

    BooleanFormula aEq246 = bvmgr.equal(a, num246);
    BooleanFormula aEq10 = bvmgr.equal(a, num10);
    BooleanFormula bEq2 = bvmgr.equal(b, num2);
    BooleanFormula bEq0 = bvmgr.equal(b, num0);
    BooleanFormula aEqNeg10 = bvmgr.equal(a, numNeg10);
    BooleanFormula bEq49 = bvmgr.equal(b, num49);
    BooleanFormula bEq1 = bvmgr.equal(b, num1);
    BooleanFormula bEqNeg1 = bvmgr.equal(b, numNeg1);
    BooleanFormula bEqNeg2 = bvmgr.equal(b, numNeg2);

    // positive numbers, signed.
    assertDivision(a, num5, true, b, aEq10, bEq2);
    assertDivision(a, num3, true, num3, aEq10);
    assertDivision(a, numNeg3, true, numNeg3, aEq10);
    assertDivision(a, b, true, num5, aEq10, bEq2);
    assertModulo(a, num5, true, num0, aEq10);
    assertModulo(a, num3, true, num1, aEq10);
    assertModulo(a, numNeg3, true, num1, aEq10);

    // positive numbers, unsigned.
    assertDivision(a, num5, false, b, aEq10, bEq2);
    assertDivision(a, num3, false, num3, aEq10);
    assertDivision(a, num253, false, num0, aEq10);
    assertDivision(a, b, false, num5, aEq10, bEq2);
    assertModulo(a, num5, false, num0, aEq10);
    assertModulo(a, num3, false, num1, aEq10);
    assertModulo(a, num253, false, num10, aEq10);

    // negative numbers, signed.
    // bitvector-division for negative numbers is C99-conform!
    assertDivision(a, num5, true, b, aEqNeg10, bEqNeg2);
    assertDivision(a, num3, true, numNeg3, aEqNeg10);
    assertDivision(a, numNeg3, true, num3, aEqNeg10);
    assertDivision(a, b, true, num5, aEqNeg10, bEqNeg2);
    assertModulo(a, num5, true, num0, aEqNeg10);
    assertModulo(a, num3, true, numNeg1, aEqNeg10);
    assertModulo(a, numNeg3, true, numNeg1, aEqNeg10);

    // negative numbers, unsigned.
    // bitvector-division for negative numbers is C99-conform!
    assertDivision(a, num5, false, b, aEq246, bEq49);
    assertDivision(a, num3, false, num82, aEq246);
    assertDivision(a, num253, false, num0, aEq246);
    assertDivision(a, b, false, num5, aEq246, bEq49);
    assertModulo(a, num5, false, num1, aEq246);
    assertModulo(a, num3, false, num0, aEq246);
    assertModulo(a, num253, false, num246, aEq246);

    // division by zero, signed.
    assertDivision(a, num0, true, b, aEq10, bEqNeg1);
    assertDivision(a, num0, true, b, aEqNeg10, bEq1);
    assertDivision(a, b, true, numNeg1, aEq10, bEq0);
    assertDivision(a, b, true, num1, aEqNeg10, bEq0);
    assertModulo(a, num0, true, numNeg10, aEqNeg10);

    // division by zero, unsigned.
    assertDivision(a, num0, false, b, aEq10, bEqNeg1);
    assertDivision(a, num0, false, b, aEqNeg10, bEqNeg1);
    assertDivision(a, b, false, numNeg1, aEq10, bEq0);
    assertDivision(a, b, false, numNeg1, aEqNeg10, bEq0);
    assertModulo(a, num0, false, a, aEqNeg10);
  }

  @Test
  public void intTest4_ModularCongruence_Simple() throws SolverException, InterruptedException {
    requireIntegers();
    final IntegerFormula x = imgr.makeVariable("x");
    final BooleanFormula f1 = imgr.modularCongruence(x, imgr.makeNumber(0), 2);
    final BooleanFormula f2 = imgr.equal(x, imgr.makeNumber(1));

    assertThatFormula(bmgr.and(f1, f2)).isUnsatisfiable();
  }

  @Test
  public void intTest4_ModularCongruence() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("int_a");
    IntegerFormula b = imgr.makeVariable("int_b");
    IntegerFormula c = imgr.makeVariable("int_c");
    IntegerFormula d = imgr.makeVariable("int_d");
    IntegerFormula num10 = imgr.makeNumber(10);
    IntegerFormula num5 = imgr.makeNumber(5);
    IntegerFormula num0 = imgr.makeNumber(0);
    IntegerFormula numNeg5 = imgr.makeNumber(-5);

    BooleanFormula fa = imgr.equal(a, num10);
    BooleanFormula fb = imgr.equal(b, num5);
    BooleanFormula fc = imgr.equal(c, num0);
    BooleanFormula fd = imgr.equal(d, numNeg5);

    // we have equal results modulo 5
    BooleanFormula fConb5 = imgr.modularCongruence(a, b, 5);
    BooleanFormula fConc5 = imgr.modularCongruence(a, c, 5);
    BooleanFormula fCond5 = imgr.modularCongruence(a, d, 5);

    // we have different results modulo 7
    BooleanFormula fConb7 = imgr.modularCongruence(a, b, 7);
    BooleanFormula fConc7 = imgr.modularCongruence(a, c, 7);
    BooleanFormula fCond7 = imgr.modularCongruence(a, d, 7);

    // check modular congruence, a=10 && b=5 && (a mod 5 = b mod 5)
    assertThatFormula(bmgr.and(fa, fb, fConb5)).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fb, bmgr.not(fConb5))).isUnsatisfiable();
    assertThatFormula(bmgr.and(fa, fc, fConc5)).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fc, bmgr.not(fConc5))).isUnsatisfiable();
    assertThatFormula(bmgr.and(fa, fd, fCond5)).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fd, bmgr.not(fCond5))).isUnsatisfiable();

    // check modular congruence, a=10 && b=5 && (a mod 7 != b mod 7)
    assertThatFormula(bmgr.and(fa, fb, fConb7)).isUnsatisfiable();
    assertThatFormula(bmgr.and(fa, fb, bmgr.not(fConb7))).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fc, fConc7)).isUnsatisfiable();
    assertThatFormula(bmgr.and(fa, fc, bmgr.not(fConc7))).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fd, fCond7)).isUnsatisfiable();
    assertThatFormula(bmgr.and(fa, fd, bmgr.not(fCond7))).isSatisfiable();
  }

  @Test
  public void intTest4_ModularCongruence_NegativeNumbers()
      throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("int_a");
    IntegerFormula b = imgr.makeVariable("int_b");
    IntegerFormula c = imgr.makeVariable("int_c");
    IntegerFormula num8 = imgr.makeNumber(8);
    IntegerFormula num3 = imgr.makeNumber(3);
    IntegerFormula numNeg2 = imgr.makeNumber(-2);

    BooleanFormula fa = imgr.equal(a, num8);
    BooleanFormula fb = imgr.equal(b, num3);
    BooleanFormula fc = imgr.equal(c, numNeg2);
    BooleanFormula fConb = imgr.modularCongruence(a, b, 5);
    BooleanFormula fConc = imgr.modularCongruence(a, c, 5);

    // check modular congruence, a=10 && b=5 && (a mod 5 = b mod 5)
    assertThatFormula(bmgr.and(fa, fb, fConb)).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fb, bmgr.not(fConb))).isUnsatisfiable();
    assertThatFormula(bmgr.and(fa, fc, fConc)).isSatisfiable();
    assertThatFormula(bmgr.and(fa, fc, bmgr.not(fConc))).isUnsatisfiable();
  }

  @Test
  public void testHardCongruence() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    IntegerFormula c = imgr.makeVariable("c");
    List<BooleanFormula> constraints = new ArrayList<>();
    Random r = new Random(42);
    int bitSize = 7; // difficulty
    BigInteger prime1 = BigInteger.probablePrime(bitSize, r);
    BigInteger prime2 = BigInteger.probablePrime(bitSize + 1, r);
    BigInteger prime3 = BigInteger.probablePrime(bitSize + 2, r);

    constraints.add(imgr.modularCongruence(imgr.add(a, imgr.makeNumber(1)), b, prime1));
    constraints.add(imgr.modularCongruence(b, c, prime2));
    constraints.add(imgr.modularCongruence(a, c, prime3));

    try (ProverEnvironment pe = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      pe.addConstraint(imgr.greaterThan(a, imgr.makeNumber(1)));
      pe.addConstraint(imgr.greaterThan(b, imgr.makeNumber(1)));
      pe.addConstraint(imgr.greaterThan(c, imgr.makeNumber(1)));
      pe.addConstraint(bmgr.and(constraints));

      assertThat(pe.isUnsat()).isFalse();

      try (Model m = pe.getModel()) {
        BigInteger aValue = m.evaluate(a);
        BigInteger bValue = m.evaluate(b);
        BigInteger cValue = m.evaluate(c);
        assertThat(aValue.add(BigInteger.ONE).subtract(bValue).mod(prime1))
            .isEqualTo(BigInteger.ZERO);
        assertThat(bValue.subtract(cValue).mod(prime2)).isEqualTo(BigInteger.ZERO);
        assertThat(aValue.subtract(cValue).mod(prime3)).isEqualTo(BigInteger.ZERO);
      }
    }
  }

  @Test
  public void realTest() throws SolverException, InterruptedException {
    requireRationals();

    RationalFormula a = rmgr.makeVariable("int_c");
    RationalFormula num = rmgr.makeNumber(1);

    BooleanFormula f = rmgr.equal(rmgr.add(a, a), num);
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testUfWithBoolType() throws SolverException, InterruptedException {
    requireIntegers();
    FunctionDeclaration<BooleanFormula> uf =
        fmgr.declareUF("fun_ib", FormulaType.BooleanType, FormulaType.IntegerType);
    BooleanFormula uf0 = fmgr.callUF(uf, imgr.makeNumber(0));
    BooleanFormula uf1 = fmgr.callUF(uf, imgr.makeNumber(1));
    BooleanFormula uf2 = fmgr.callUF(uf, imgr.makeNumber(2));

    BooleanFormula f01 = bmgr.xor(uf0, uf1);
    BooleanFormula f02 = bmgr.xor(uf0, uf2);
    BooleanFormula f12 = bmgr.xor(uf1, uf2);
    assertThatFormula(f01).isSatisfiable();
    assertThatFormula(f02).isSatisfiable();
    assertThatFormula(f12).isSatisfiable();

    BooleanFormula f = bmgr.and(f01, f02, f12);
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testUfWithBoolArg() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support boolean arguments", solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    requireIntegers();
    FunctionDeclaration<IntegerFormula> uf =
        fmgr.declareUF("fun_bi", FormulaType.IntegerType, FormulaType.BooleanType);
    IntegerFormula ufTrue = fmgr.callUF(uf, bmgr.makeBoolean(true));
    IntegerFormula ufFalse = fmgr.callUF(uf, bmgr.makeBoolean(false));

    BooleanFormula f = bmgr.not(imgr.equal(ufTrue, ufFalse));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void quantifierEliminationTest1() throws SolverException, InterruptedException {
    requireQuantifiers();
    requireIntegers();

    IntegerFormula var_B = imgr.makeVariable("b");
    IntegerFormula var_C = imgr.makeVariable("c");
    IntegerFormula num_2 = imgr.makeNumber(2);
    IntegerFormula num_1000 = imgr.makeNumber(1000);
    BooleanFormula eq_c_2 = imgr.equal(var_C, num_2);
    IntegerFormula minus_b_c = imgr.subtract(var_B, var_C);
    BooleanFormula gt_bMinusC_1000 = imgr.greaterThan(minus_b_c, num_1000);
    BooleanFormula and_cEq2_bMinusCgt1000 = bmgr.and(eq_c_2, gt_bMinusC_1000);

    BooleanFormula f = qmgr.exists(ImmutableList.of(var_C), and_cEq2_bMinusCgt1000);
    BooleanFormula result = qmgr.eliminateQuantifiers(f);
    assertThat(result.toString()).doesNotContain("exists");
    assertThat(result.toString()).doesNotContain("c");

    BooleanFormula expected = imgr.greaterOrEquals(var_B, imgr.makeNumber(1003));
    assertThatFormula(result).isEquivalentTo(expected);
  }

  @Test
  @Ignore
  public void quantifierEliminationTest2() throws SolverException, InterruptedException {
    requireQuantifiers();
    requireIntegers();

    IntegerFormula i1 = imgr.makeVariable("i@1");
    IntegerFormula j1 = imgr.makeVariable("j@1");
    IntegerFormula j2 = imgr.makeVariable("j@2");
    IntegerFormula a1 = imgr.makeVariable("a@1");

    IntegerFormula _1 = imgr.makeNumber(1);
    IntegerFormula _minus1 = imgr.makeNumber(-1);

    IntegerFormula _1_plus_a1 = imgr.add(_1, a1);
    BooleanFormula not_j1_eq_minus1 = bmgr.not(imgr.equal(j1, _minus1));
    BooleanFormula i1_eq_1_plus_a1 = imgr.equal(i1, _1_plus_a1);

    IntegerFormula j2_plus_a1 = imgr.add(j2, a1);
    BooleanFormula j1_eq_j2_plus_a1 = imgr.equal(j1, j2_plus_a1);

    BooleanFormula fm = bmgr.and(i1_eq_1_plus_a1, not_j1_eq_minus1, j1_eq_j2_plus_a1);

    BooleanFormula q = qmgr.exists(ImmutableList.of(j1), fm);
    BooleanFormula result = qmgr.eliminateQuantifiers(q);
    assertThat(result.toString()).doesNotContain("exists");
    assertThat(result.toString()).doesNotContain("j@1");

    BooleanFormula expected = bmgr.not(imgr.equal(i1, j2));
    assertThatFormula(result).isEquivalentTo(expected);
  }

  @Test
  public void testGetFormulaType() {
    requireIntegers();
    BooleanFormula _boolVar = bmgr.makeVariable("boolVar");
    assertThat(mgr.getFormulaType(_boolVar)).isEqualTo(FormulaType.BooleanType);

    IntegerFormula _intVar = imgr.makeNumber(1);
    assertThat(mgr.getFormulaType(_intVar)).isEqualTo(FormulaType.IntegerType);

    requireArrays();
    ArrayFormula<IntegerFormula, IntegerFormula> _arrayVar =
        amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);
    assertThat(mgr.getFormulaType(_arrayVar)).isInstanceOf(FormulaType.ArrayFormulaType.class);
  }

  @Test
  public void testMakeIntArray() {
    requireArrays();
    requireIntegers();

    IntegerFormula _i = imgr.makeVariable("i");
    IntegerFormula _1 = imgr.makeNumber(1);
    IntegerFormula _i_plus_1 = imgr.add(_i, _1);

    ArrayFormula<IntegerFormula, IntegerFormula> _b =
        amgr.makeArray("b", FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula _b_at_i_plus_1 = amgr.select(_b, _i_plus_1);

    switch (solver) {
      case MATHSAT5:
        // Mathsat5 has a different internal representation of the formula
        assertThat(_b_at_i_plus_1.toString()).isEqualTo("(`read_int_int` b (`+_int` i 1))");
        break;
      case PRINCESS:
        assertThat(_b_at_i_plus_1.toString()).isEqualTo("select(b, (i + 1))");
        break;
      case OPENSMT:
        // INFO: OpenSmt changes the order of the terms in the sum
        assertThat(_b_at_i_plus_1.toString()).isEqualTo("(select b (+ 1 i))");
        break;
      default:
        assertThat(_b_at_i_plus_1.toString())
            .isEqualTo("(select b (+ i 1))"); // Compatibility to all solvers not guaranteed
    }
  }

  @Test
  public void testMakeBitVectorArray() {
    requireArrays();
    requireBitvectors();

    assume()
        .withMessage("Solver does not support bit-vector arrays.")
        .that(solver)
        .isNotEqualTo(Solvers.PRINCESS);

    BitvectorFormula _i = mgr.getBitvectorFormulaManager().makeVariable(64, "i");
    ArrayFormula<BitvectorFormula, BitvectorFormula> _b =
        amgr.makeArray(
            "b",
            FormulaType.getBitvectorTypeWithSize(64),
            FormulaType.getBitvectorTypeWithSize(32));
    BitvectorFormula _b_at_i = amgr.select(_b, _i);

    switch (solver) {
      case MATHSAT5:
        // Mathsat5 has a different internal representation of the formula
        assertThat(_b_at_i.toString()).isEqualTo("(`read_T(18)_T(20)` b i)");
        break;
      case BOOLECTOR:
        assume()
            .withMessage("Solver %s does not printing formulae.", solverToUse())
            .that(solver)
            .isNotEqualTo(Solvers.BOOLECTOR);
        break;
      default:
        assertThat(_b_at_i.toString())
            .isEqualTo("(select b i)"); // Compatibility to all solvers not guaranteed
    }
  }

  @Test
  public void testNestedIntegerArray() {
    requireArrays();
    requireIntegers();

    IntegerFormula _i = imgr.makeVariable("i");
    ArrayFormula<IntegerFormula, ArrayFormula<IntegerFormula, IntegerFormula>> multi =
        amgr.makeArray(
            "multi",
            FormulaType.IntegerType,
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType));

    IntegerFormula valueInMulti = amgr.select(amgr.select(multi, _i), _i);

    switch (solver) {
      case MATHSAT5:
        assertThat(valueInMulti.toString())
            .isEqualTo("(`read_int_int` (`read_int_T(17)` multi i) i)");
        break;
      case PRINCESS:
        assertThat(valueInMulti.toString()).isEqualTo("select(select(multi, i), i)");
        break;
      default:
        assertThat(valueInMulti.toString()).isEqualTo("(select (select multi i) i)");
    }
  }

  @Test
  public void testNestedRationalArray() {
    requireArrays();
    requireRationals();
    requireIntegers();

    IntegerFormula _i = imgr.makeVariable("i");
    ArrayFormula<IntegerFormula, ArrayFormula<IntegerFormula, RationalFormula>> multi =
        amgr.makeArray(
            "multi",
            FormulaType.IntegerType,
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.RationalType));

    RationalFormula valueInMulti = amgr.select(amgr.select(multi, _i), _i);

    switch (solver) {
      case MATHSAT5:
        assertThat(valueInMulti.toString())
            .isEqualTo("(`read_int_rat` (`read_int_T(17)` multi i) i)");
        break;
      case PRINCESS:
        assertThat(valueInMulti.toString()).isEqualTo("select(select(multi, i), i)");
        break;
      default:
        assertThat(valueInMulti.toString()).isEqualTo("(select (select multi i) i)");
    }
  }

  @Test
  public void testNestedBitVectorArray() {
    requireArrays();
    requireBitvectors();
    requireIntegers();

    assume()
        .withMessage("Solver does not support bit-vector arrays.")
        .that(solver)
        .isNotEqualTo(Solvers.PRINCESS);

    IntegerFormula _i = imgr.makeVariable("i");
    ArrayFormula<IntegerFormula, ArrayFormula<IntegerFormula, BitvectorFormula>> multi =
        amgr.makeArray(
            "multi",
            FormulaType.IntegerType,
            FormulaType.getArrayType(
                FormulaType.IntegerType, FormulaType.getBitvectorTypeWithSize(32)));

    BitvectorFormula valueInMulti = amgr.select(amgr.select(multi, _i), _i);

    switch (solver) {
      case MATHSAT5:
        String readWrite = "(`read_int_T(18)` (`read_int_T(19)` multi i) i)";
        assertThat(valueInMulti.toString()).isEqualTo(readWrite);
        break;
      default:
        assertThat(valueInMulti.toString()).isEqualTo("(select (select multi i) i)");
    }
  }

  @Test
  public void nonLinearMultiplication() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula i2 = imgr.makeNumber(2);
    IntegerFormula i3 = imgr.makeNumber(3);
    IntegerFormula i4 = imgr.makeNumber(4);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    IntegerFormula x_mult_y;
    try {
      x_mult_y = imgr.multiply(x, y);
    } catch (UnsupportedOperationException e) {
      // do nothing, this exception is fine here, because solvers do not need
      // to support non-linear arithmetic, we can then skip the test completely
      throw new AssumptionViolatedException("Support for non-linear arithmetic is optional", e);
    }

    BooleanFormula x_equal_2 = imgr.equal(i2, x);
    BooleanFormula y_equal_3 = imgr.equal(i3, y);
    BooleanFormula z_equal_4 = imgr.equal(i4, z);
    BooleanFormula z_equal_x_mult_y = imgr.equal(z, x_mult_y);

    try (ProverEnvironment env = context.newProverEnvironment()) {
      env.push(x_equal_2);
      env.push(y_equal_3);
      env.push(z_equal_4);
      env.push(z_equal_x_mult_y);
      assertThat(env).isUnsatisfiable();
    }
  }

  @Test
  public void composedLinearMultiplication() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula i2 = imgr.makeNumber(2);
    IntegerFormula i3 = imgr.makeNumber(3);
    IntegerFormula i4 = imgr.makeNumber(4);
    IntegerFormula x = imgr.makeVariable("x");

    // MULT should be supported by all solvers, DIV/MOD are missing in Mathsat.
    IntegerFormula mult = imgr.multiply(x, imgr.add(i2, imgr.add(i3, i4)));
    IntegerFormula div;
    IntegerFormula mod;
    try {
      div = imgr.divide(x, imgr.add(i2, imgr.add(i3, i4)));
      mod = imgr.modulo(x, imgr.add(i2, imgr.add(i3, i4)));
    } catch (UnsupportedOperationException e) {
      // do nothing, this exception is fine here, because solvers do not need
      // to support non-linear arithmetic, we can then skip the test completely
      throw new AssumptionViolatedException("Support for non-linear arithmetic is optional", e);
    }

    try (ProverEnvironment env = context.newProverEnvironment()) {
      env.push(imgr.greaterThan(mult, i4));
      env.push(imgr.greaterThan(div, i4));
      env.push(imgr.greaterThan(mod, i2));
      assertThat(env).isSatisfiable();
    }
  }

  @Test
  public void multiplicationSquares() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula i2 = imgr.makeNumber(2);
    IntegerFormula i3 = imgr.makeNumber(3);
    IntegerFormula i4 = imgr.makeNumber(4);
    IntegerFormula i5 = imgr.makeNumber(5);

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    IntegerFormula xx;
    IntegerFormula yy;
    IntegerFormula zz;
    try {
      xx = imgr.multiply(x, x);
      yy = imgr.multiply(y, y);
      zz = imgr.multiply(z, z);
    } catch (UnsupportedOperationException e) {
      // do nothing, this exception is fine here, because solvers do not need
      // to support non-linear arithmetic, we can then skip the test completely
      throw new AssumptionViolatedException("Support for non-linear arithmetic is optional", e);
    }

    try (ProverEnvironment env = context.newProverEnvironment()) {
      // check x*x + y*y = z*z
      env.push(imgr.equal(zz, imgr.add(xx, yy)));

      {
        // SAT with x=4 and y=3
        env.push(imgr.equal(x, i3));
        env.push(imgr.equal(y, i4));
        assertThat(env).isSatisfiable();
        env.pop();
        env.pop();
      }
      { // SAT with z=5
        env.push(imgr.equal(z, i5));
        assertThat(env).isSatisfiable();
        env.pop();
      }
      {
        // UNSAT with z=5 and x=2
        env.push(imgr.equal(z, i5));
        env.push(imgr.equal(x, i2));
        assertThat(env).isUnsatisfiable();
        env.pop();
        env.pop();
      }
      { // UNSAT with z=5 and x>3 and y>3
        env.push(imgr.equal(z, i5));
        env.push(imgr.greaterThan(x, i3));
        env.push(imgr.greaterThan(y, i3));
        assertThat(env).isUnsatisfiable();
        env.pop();
        env.pop();
        env.pop();
      }
    }
  }

  @Test
  public void multiplicationFactors() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula i37 = imgr.makeNumber(37);
    IntegerFormula i1 = imgr.makeNumber(1);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");

    IntegerFormula x_mult_y;
    try {
      x_mult_y = imgr.multiply(x, y);
    } catch (UnsupportedOperationException e) {
      // do nothing, this exception is fine here, because solvers do not need
      // to support non-linear arithmetic, we can then skip the test completely
      throw new AssumptionViolatedException("Support for non-linear arithmetic is optional", e);
    }

    try (ProverEnvironment env = context.newProverEnvironment()) {
      env.push(imgr.equal(x_mult_y, i37));
      assertThat(env).isSatisfiable();
      env.push(imgr.greaterThan(x, i1));
      env.push(imgr.greaterThan(y, i1));
      assertThat(env).isUnsatisfiable();
    }
  }

  @Test
  public void multiplicationCubic() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula i125 = imgr.makeNumber(125);
    IntegerFormula i27 = imgr.makeNumber(27);
    IntegerFormula i5 = imgr.makeNumber(5);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");

    IntegerFormula xxx;
    IntegerFormula yyy;
    try {
      xxx = imgr.multiply(x, imgr.multiply(x, x));
      yyy = imgr.multiply(y, imgr.multiply(y, y));
    } catch (UnsupportedOperationException e) {
      // do nothing, this exception is fine here, because solvers do not need
      // to support non-linear arithmetic, we can then skip the test completely
      throw new AssumptionViolatedException("Support for non-linear arithmetic is optional", e);
    }

    try (ProverEnvironment env = context.newProverEnvironment()) {
      env.push(imgr.equal(xxx, i125));
      env.push(imgr.equal(yyy, i27));
      assertThat(env).isSatisfiable();
      env.push(imgr.lessThan(x, i5));
      assertThat(env).isUnsatisfiable();
    }

    try (ProverEnvironment env = context.newProverEnvironment()) {
      env.push(imgr.equal(imgr.add(xxx, yyy), imgr.add(i27, i125)));
      env.push(imgr.lessThan(y, i5));
      env.push(imgr.equal(x, i5));
      assertThat(env).isSatisfiable();
      env.pop();
      env.push(imgr.lessThan(x, i5));
      assertThat(env).isUnsatisfiable();
    }
  }

  @Test
  public void nonLinearDivision() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula i2 = imgr.makeNumber(2);
    IntegerFormula i3 = imgr.makeNumber(3);
    IntegerFormula i4 = imgr.makeNumber(4);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    IntegerFormula x_div_y;
    try {
      x_div_y = imgr.divide(x, y);
    } catch (UnsupportedOperationException e) {
      // do nothing, this exception is fine here, because solvers do not need
      // to support non-linear arithmetic, we can then skip the test completely
      throw new AssumptionViolatedException("Support for non-linear arithmetic is optional", e);
    }

    BooleanFormula x_equal_4 = imgr.equal(i4, x);
    BooleanFormula y_equal_2 = imgr.equal(i2, y);
    BooleanFormula z_equal_3 = imgr.equal(i3, z);
    BooleanFormula z_equal_x_div_y = imgr.equal(z, x_div_y);

    try (ProverEnvironment env = context.newProverEnvironment()) {
      env.push(x_equal_4);
      env.push(y_equal_2);
      env.push(z_equal_3);
      env.push(z_equal_x_div_y);
      assertThat(env).isUnsatisfiable();
    }
  }

  @Test
  public void integerDivisionRounding() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula varSeven = imgr.makeVariable("a");
    IntegerFormula varEight = imgr.makeVariable("b");

    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula three = imgr.makeNumber(3);

    // Test that 8/3 and 7/3 are rounded as expected for all combinations of positive/negative
    // numbers
    BooleanFormula f =
        bmgr.and(
            imgr.equal(varSeven, imgr.makeNumber(7)),
            imgr.equal(varEight, imgr.makeNumber(8)),
            imgr.equal(imgr.divide(varSeven, three), two),
            imgr.equal(imgr.divide(imgr.negate(varSeven), three), imgr.negate(three)),
            imgr.equal(imgr.divide(varSeven, imgr.negate(three)), imgr.negate(two)),
            imgr.equal(imgr.divide(imgr.negate(varSeven), imgr.negate(three)), three),
            imgr.equal(imgr.divide(varEight, three), two),
            imgr.equal(imgr.divide(imgr.negate(varEight), three), imgr.negate(three)),
            imgr.equal(imgr.divide(varEight, imgr.negate(three)), imgr.negate(two)),
            imgr.equal(imgr.divide(imgr.negate(varEight), imgr.negate(three)), three));

    assertThatFormula(f).isSatisfiable();
  }

  private static final ImmutableSet<Solvers> VAR_TRACKING_SOLVERS =
      ImmutableSet.of(
          Solvers.SMTINTERPOL,
          Solvers.MATHSAT5,
          Solvers.CVC4,
          Solvers.CVC5,
          Solvers.BOOLECTOR,
          Solvers.YICES2,
          Solvers.OPENSMT);

  private static final ImmutableSet<Solvers> VAR_AND_UF_TRACKING_SOLVERS =
      ImmutableSet.of(
          Solvers.SMTINTERPOL,
          Solvers.MATHSAT5,
          Solvers.BOOLECTOR,
          Solvers.YICES2,
          Solvers.OPENSMT);

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testVariableWithDifferentSort() {
    assume().that(solverToUse()).isNotIn(VAR_TRACKING_SOLVERS);
    bmgr.makeVariable("x");
    if (imgr != null) {
      imgr.makeVariable("x");
    } else if (bvmgr != null) {
      bvmgr.makeVariable(8, "x");
    }
  }

  @Test(expected = Exception.class) // complement of above test case
  @SuppressWarnings("CheckReturnValue")
  public void testFailOnVariableWithDifferentSort() {
    assume().that(solverToUse()).isIn(VAR_TRACKING_SOLVERS);
    bmgr.makeVariable("x");
    if (imgr != null) {
      imgr.makeVariable("x");
    } else if (bvmgr != null) {
      bvmgr.makeVariable(8, "x");
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testVariableAndUFWithDifferentSort() {
    assume().that(solverToUse()).isNotIn(VAR_AND_UF_TRACKING_SOLVERS);
    bmgr.makeVariable("y");
    fmgr.declareUF("y", FormulaType.BooleanType, FormulaType.BooleanType);
  }

  @Test(expected = Exception.class) // complement of above test case
  @SuppressWarnings("CheckReturnValue")
  public void testFailOnVariableAndUFWithDifferentSort() {
    assume().that(solverToUse()).isIn(VAR_AND_UF_TRACKING_SOLVERS);
    bmgr.makeVariable("y");
    fmgr.declareUF("y", FormulaType.BooleanType, FormulaType.BooleanType);
  }

  @Test(expected = Exception.class) // different ordering of above test case
  @SuppressWarnings("CheckReturnValue")
  public void testFailOnUFAndVariableWithDifferentSort() {
    assume().that(solverToUse()).isIn(VAR_AND_UF_TRACKING_SOLVERS);
    fmgr.declareUF("y", FormulaType.BooleanType, FormulaType.BooleanType);
    bmgr.makeVariable("y");
  }

  @Test
  public void testVariableAndUFWithEqualSort() {
    assume()
        .withMessage("Solver %s does not support UFs without arguments", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.BOOLECTOR, Solvers.CVC5, Solvers.BITWUZLA);

    BooleanFormula z1 = bmgr.makeVariable("z");
    BooleanFormula z2 = fmgr.declareAndCallUF("z", FormulaType.BooleanType);
    if (ImmutableSet.of(Solvers.CVC4, Solvers.PRINCESS).contains(solverToUse())) {
      assertThat(z1).isNotEqualTo(z2);
    } else {
      assertThat(z1).isEqualTo(z2);
    }
  }
}
