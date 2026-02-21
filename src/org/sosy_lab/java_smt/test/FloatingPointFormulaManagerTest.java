// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.getFloatingPointTypeFromSizesWithHiddenBit;
import static org.sosy_lab.java_smt.api.FormulaType.getFloatingPointTypeFromSizesWithoutHiddenBit;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

public class FloatingPointFormulaManagerTest
    extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // numbers are small enough to be precise with single precision
  private static final int[] SINGLE_PREC_INTS = new int[] {0, 1, 2, 5, 10, 20, 50, 100, 200, 500};

  // Multiple distinct NaN numbers (not all, just some common ones) as defined in IEEE 754-2008 as
  // 32 bit bitvectors for single-precision floating-point numbers. All bitvectors are defined as
  // IEEE 754 (sign bit + exponent bits + mantissa bits (without hidden bit))
  private static final Set<String> SINGLE_PRECISION_NANS_BITWISE =
      ImmutableSet.of(
          "01111111110000000000000000000000",
          "11111111110000000000000000000000",
          "01111111100000000000000000000001",
          "11111111100000000000000000000001",
          "01111111111111111111111111111111",
          "11111111111111111111111111111111",
          "01111111100000000000000000001100");
  // Other special FP values (single precision, defined as above)
  private static final String SINGLE_PRECISION_POSITIVE_INFINITY_BITWISE =
      "01111111100000000000000000000000";
  private static final String SINGLE_PRECISION_NEGATIVE_INFINITY_BITWISE =
      "11111111100000000000000000000000";
  private static final String SINGLE_PRECISION_POSITIVE_ZERO_BITWISE =
      "00000000000000000000000000000000";
  private static final String SINGLE_PRECISION_NEGATIVE_ZERO_BITWISE =
      "10000000000000000000000000000000";

  private static final int NUM_RANDOM_TESTS = 50;

  private FloatingPointType singlePrecType;
  private FloatingPointType doublePrecType;
  private FloatingPointFormula nan;
  private FloatingPointFormula posInf;
  private FloatingPointFormula negInf;
  private FloatingPointFormula zero;
  private FloatingPointFormula one;
  private FloatingPointFormula negZero;

  @Before
  public void init() {
    requireFloats();

    singlePrecType = FormulaType.getSinglePrecisionFloatingPointType();
    doublePrecType = FormulaType.getDoublePrecisionFloatingPointType();
    nan = fpmgr.makeNaN(singlePrecType);
    posInf = fpmgr.makePlusInfinity(singlePrecType);
    negInf = fpmgr.makeMinusInfinity(singlePrecType);
    zero = fpmgr.makeNumber(0.0, singlePrecType);
    negZero = fpmgr.makeNumber(-0.0, singlePrecType);
    one = fpmgr.makeNumber(1.0, singlePrecType);
  }

  @Test
  public void testSpecialNumberIdentity() {
    assertThat(fpmgr.makeNaN(singlePrecType)).isEqualTo(nan);
    assertThat(fpmgr.makePlusInfinity(singlePrecType)).isEqualTo(posInf);
    assertThat(fpmgr.makeMinusInfinity(singlePrecType)).isEqualTo(negInf);
    assertThat(fpmgr.makeNumber(0.0, singlePrecType)).isEqualTo(zero);
    assertThat(fpmgr.makeNumber(-0.0, singlePrecType)).isEqualTo(negZero);

    assertThat(fpmgr.makeNaN(doublePrecType)).isEqualTo(fpmgr.makeNaN(doublePrecType));
    assertThat(fpmgr.makePlusInfinity(doublePrecType))
        .isEqualTo(fpmgr.makePlusInfinity(doublePrecType));
    assertThat(fpmgr.makeMinusInfinity(doublePrecType))
        .isEqualTo(fpmgr.makeMinusInfinity(doublePrecType));
    assertThat(fpmgr.makeNumber(0.0, doublePrecType))
        .isEqualTo(fpmgr.makeNumber(0.0, doublePrecType));
    assertThat(fpmgr.makeNumber(-0.0, doublePrecType))
        .isEqualTo(fpmgr.makeNumber(-0.0, doublePrecType));

    // Different precisions should not be equal
    assertThat(fpmgr.makeNaN(doublePrecType)).isNotEqualTo(nan);
    assertThat(fpmgr.makePlusInfinity(doublePrecType)).isNotEqualTo(posInf);
    assertThat(fpmgr.makeMinusInfinity(doublePrecType)).isNotEqualTo(negInf);
    assertThat(fpmgr.makeNumber(0.0, doublePrecType)).isNotEqualTo(zero);
    assertThat(fpmgr.makeNumber(-0.0, doublePrecType)).isNotEqualTo(negZero);
  }

  @Test
  public void floatingPointType() {
    FloatingPointType type = getFloatingPointTypeFromSizesWithoutHiddenBit(23, 42);
    FloatingPointFormula var = fpmgr.makeVariable("x", type);
    FloatingPointType result = (FloatingPointType) mgr.getFormulaType(var);

    assertWithMessage("exponent sizes not equal")
        .that(result.getExponentSize())
        .isEqualTo(type.getExponentSize());
    assertWithMessage("mantissa sizes not equal")
        .that(result.getMantissaSizeWithHiddenBit())
        .isEqualTo(type.getMantissaSizeWithHiddenBit());
  }

  @Test
  public void roundingModeVisitor() {
    FloatingPointFormula variable =
        fpmgr.makeVariable("a", FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula original =
        fpmgr.sqrt(variable, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    for (FloatingPointRoundingMode rm : FloatingPointRoundingMode.values()) {
      if (solver == Solvers.MATHSAT5 && rm == FloatingPointRoundingMode.NEAREST_TIES_AWAY) {
        // SKIP MathSAT does not support rounding mode "nearest-ties-away"
        continue;
      }
      // Build a term with a different rounding mode, then replace it in the visitor
      FloatingPointFormula substituted =
          (FloatingPointFormula)
              mgr.visit(
                  fpmgr.sqrt(variable, rm),
                  new FormulaVisitor<Formula>() {
                    @Override
                    public Formula visitFreeVariable(Formula f, String name) {
                      return f;
                    }

                    @Override
                    public Formula visitConstant(Formula f, Object value) {
                      assertThat(f).isInstanceOf(FloatingPointRoundingModeFormula.class);
                      assertThat(value).isInstanceOf(FloatingPointRoundingMode.class);
                      assertThat(value).isEqualTo(rm);

                      // Return the default rounding mode
                      return fpmgr.makeRoundingMode(FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
                    }

                    @Override
                    public Formula visitFunction(
                        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
                      assertThat(functionDeclaration.getKind())
                          .isEqualTo(FunctionDeclarationKind.FP_SQRT);
                      assertThat(args).hasSize(2);
                      return mgr.makeApplication(
                          functionDeclaration,
                          mgr.visit(args.get(0), this),
                          mgr.visit(args.get(1), this));
                    }

                    @Override
                    public Formula visitQuantifier(
                        BooleanFormula f,
                        Quantifier quantifier,
                        List<Formula> boundVariables,
                        BooleanFormula body) {
                      throw new IllegalArgumentException(
                          String.format("Unexpected quantifier %s", quantifier));
                    }
                  });

      // Check that after the substitution the rounding mode is the default again
      assertThat(original).isEqualTo(substituted);
    }
  }

  @Test
  public void negative() throws SolverException, InterruptedException {
    for (double d : new double[] {-1, -2, -0.0, Double.NEGATIVE_INFINITY}) {
      FloatingPointFormula formula = fpmgr.makeNumber(d, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isTautological();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isUnsatisfiable();
      assertEqualsAsFp(fpmgr.negate(formula), fpmgr.abs(formula));
    }
    for (double d : new double[] {1, 2, 0.0, Double.POSITIVE_INFINITY}) {
      FloatingPointFormula formula = fpmgr.makeNumber(d, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isTautological();
      assertEqualsAsFp(formula, fpmgr.abs(formula));
    }
  }

  @Test
  public void parser() throws SolverException, InterruptedException {
    for (String s :
        new String[] {
          "-1",
          "-Infinity",
          "-0",
          "-0.0",
          "-0.000",
          "-0e5",
          "-0.00e-5",
          "-12e34",
          "-12e-34",
          "-12.34E56",
          "-12.34e-56",
        }) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isTautological();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isUnsatisfiable();
      assertEqualsAsFp(fpmgr.negate(formula), fpmgr.abs(formula));
    }
    for (String s :
        new String[] {
          "1",
          "Infinity",
          "0",
          "0.0",
          "0.000",
          "0e5",
          "0.00e-5",
          "12e34",
          "12e-34",
          "12.34E56",
          "12.34e-56",
        }) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isTautological();
      assertEqualsAsFp(formula, fpmgr.abs(formula));
    }
    for (String s :
        new String[] {
          "+1",
          "+Infinity",
          "+0",
          "+0.0",
          "+0.000",
          "+0e5",
          "+0.00e-5",
          "+12e34",
          "+12e-34",
          "+12.34E56",
          "+12.34e-56",
        }) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isTautological();
      assertEqualsAsFp(formula, fpmgr.abs(formula));
    }
    // NaN is not positive and not negative.
    for (String s : new String[] {"NaN", "-NaN", "+NaN"}) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isUnsatisfiable();
    }
  }

  @Test
  public void negativeZeroDivision() throws SolverException, InterruptedException {
    BooleanFormula formula =
        fpmgr.equalWithFPSemantics(
            fpmgr.divide(one, negZero, FloatingPointRoundingMode.TOWARD_ZERO),
            fpmgr.makeMinusInfinity(singlePrecType));
    assertThatFormula(formula).isSatisfiable();
    assertThatFormula(bmgr.not(formula)).isUnsatisfiable();
  }

  @Test
  public void nanEqualNanIsUnsat() throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.equalWithFPSemantics(nan, nan)).isUnsatisfiable();
  }

  @Test
  public void nanAssignedNanIsTrue() throws SolverException, InterruptedException {
    assertEqualsAsFormula(nan, nan);
  }

  @Test
  public void nanOrdering() throws SolverException, InterruptedException {
    for (FloatingPointFormula other : new FloatingPointFormula[] {zero, posInf, negInf}) {
      assertThatFormula(fpmgr.greaterThan(nan, other)).isUnsatisfiable();
      assertThatFormula(fpmgr.greaterOrEquals(nan, other)).isUnsatisfiable();
      assertThatFormula(fpmgr.lessThan(nan, other)).isUnsatisfiable();
      assertThatFormula(fpmgr.lessOrEquals(nan, other)).isUnsatisfiable();
      assertEqualsAsFormula(fpmgr.max(nan, other), other);
      assertEqualsAsFormula(fpmgr.min(nan, other), other);

      assertThatFormula(fpmgr.greaterThan(other, nan)).isUnsatisfiable();
      assertThatFormula(fpmgr.greaterOrEquals(other, nan)).isUnsatisfiable();
      assertThatFormula(fpmgr.lessThan(other, nan)).isUnsatisfiable();
      assertThatFormula(fpmgr.lessOrEquals(other, nan)).isUnsatisfiable();
      assertEqualsAsFormula(fpmgr.max(other, nan), other);
      assertEqualsAsFormula(fpmgr.min(other, nan), other);
    }
  }

  @Test
  public void infinityOrdering() throws SolverException, InterruptedException {
    BooleanFormula order1 = fpmgr.greaterThan(posInf, zero);
    BooleanFormula order2 = fpmgr.greaterThan(zero, negInf);
    BooleanFormula order3 = fpmgr.greaterThan(posInf, negInf);

    assertThatFormula(bmgr.and(order1, order2, order3)).isTautological();

    assertEqualsAsFp(fpmgr.max(posInf, zero), posInf);
    assertEqualsAsFp(fpmgr.max(posInf, negInf), posInf);
    assertEqualsAsFp(fpmgr.max(negInf, zero), zero);
    assertEqualsAsFp(fpmgr.min(posInf, zero), zero);
    assertEqualsAsFp(fpmgr.min(posInf, negInf), negInf);
    assertEqualsAsFp(fpmgr.min(negInf, zero), negInf);
  }

  @Test
  public void infinityVariableOrdering() throws SolverException, InterruptedException {
    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    BooleanFormula varIsNan = fpmgr.isNaN(var);

    BooleanFormula order1 = fpmgr.greaterOrEquals(posInf, var);
    BooleanFormula order2 = fpmgr.lessOrEquals(negInf, var);

    assertThatFormula(bmgr.or(varIsNan, bmgr.and(order1, order2))).isTautological();
  }

  @Test
  public void sqrt() throws SolverException, InterruptedException {
    for (double d : new double[] {0.25, 1, 2, 4, 9, 15, 1234, 1000000}) {
      assertEqualsAsFp(
          fpmgr.sqrt(fpmgr.makeNumber(d * d, doublePrecType)), fpmgr.makeNumber(d, doublePrecType));
      assertEqualsAsFp(
          fpmgr.sqrt(fpmgr.makeNumber(d, doublePrecType)),
          fpmgr.makeNumber(Math.sqrt(d), doublePrecType));
      assertThatFormula(fpmgr.isNaN(fpmgr.sqrt(fpmgr.makeNumber(-d, doublePrecType))))
          .isTautological();
    }
  }

  @Test
  public void fpRemainderNormal() throws SolverException, InterruptedException {
    assume()
        .withMessage("MathSAT5 does not implement fp.rem")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    for (FloatingPointType prec :
        new FloatingPointType[] {
          singlePrecType, doublePrecType, getFloatingPointTypeFromSizesWithoutHiddenBit(5, 6),
        }) {

      final FloatingPointFormula numFive = fpmgr.makeNumber(5, prec);
      final FloatingPointFormula numFour = fpmgr.makeNumber(4, prec);
      final FloatingPointFormula numSix = fpmgr.makeNumber(6, prec);

      final FloatingPointFormula numOne = fpmgr.makeNumber(1, prec);
      final FloatingPointFormula numMinusOne = fpmgr.makeNumber(-1, prec);

      assertEqualsAsFormula(fpmgr.remainder(numFive, numFour), numOne);
      assertEqualsAsFormula(fpmgr.remainder(numFive, numSix), numMinusOne);
    }
  }

  @Test
  public void fpRemainderSpecial() throws SolverException, InterruptedException {
    assume()
        .withMessage("MathSAT5 does not implement fp.rem")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    for (FloatingPointType prec :
        new FloatingPointType[] {
          singlePrecType, doublePrecType, getFloatingPointTypeFromSizesWithoutHiddenBit(5, 6),
        }) {

      final FloatingPointFormula num = fpmgr.makeNumber(42, prec);

      final FloatingPointFormula fpNan = fpmgr.makeNumber("NaN", prec);
      final FloatingPointFormula fpZero = fpmgr.makeNumber("0", prec);
      final FloatingPointFormula fpInf = fpmgr.makePlusInfinity(prec);

      final FloatingPointFormula minusNan = fpmgr.makeNumber("-NaN", prec);
      final FloatingPointFormula minusZero = fpmgr.makeNumber("0", prec);
      final FloatingPointFormula minusInf = fpmgr.makeMinusInfinity(prec);

      assertEqualsAsFormula(fpmgr.remainder(fpNan, fpNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(fpZero, fpZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(fpInf, fpInf), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(minusNan, minusNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(minusZero, minusZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(minusInf, minusInf), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, fpNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, fpZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, fpInf), num);
      assertEqualsAsFormula(fpmgr.remainder(num, minusNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, minusZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, minusInf), num);
    }
  }

  @Test
  public void specialValueFunctions() throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.isInfinity(posInf)).isTautological();
    assertThatFormula(fpmgr.isNormal(posInf)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(posInf)).isUnsatisfiable();

    assertThatFormula(fpmgr.isInfinity(negInf)).isTautological();
    assertThatFormula(fpmgr.isNormal(negInf)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(negInf)).isUnsatisfiable();

    assertThatFormula(fpmgr.isNaN(nan)).isTautological();
    assertThatFormula(fpmgr.isNormal(nan)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(nan)).isUnsatisfiable();

    assertThatFormula(fpmgr.isZero(zero)).isTautological();
    assertThatFormula(fpmgr.isSubnormal(zero)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(zero)).isUnsatisfiable();

    assertThatFormula(fpmgr.isZero(negZero)).isTautological();
    assertThatFormula(fpmgr.equalWithFPSemantics(zero, negZero)).isTautological();
    assertThatFormula(fpmgr.isSubnormal(negZero)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(negZero)).isUnsatisfiable();

    FloatingPointFormula minPosNormalValue = fpmgr.makeNumber(Float.MIN_NORMAL, singlePrecType);
    assertThatFormula(fpmgr.isSubnormal(minPosNormalValue)).isUnsatisfiable();
    assertThatFormula(fpmgr.isNormal(minPosNormalValue)).isSatisfiable();
    assertThatFormula(fpmgr.isZero(minPosNormalValue)).isUnsatisfiable();
  }

  @Test
  public void specialValueFunctionsFrom32Bits() throws SolverException, InterruptedException {
    float posInfFromBits = Float.intBitsToFloat(0x7f80_0000);
    assertThatFormula(fpmgr.isInfinity(fpmgr.makeNumber(posInfFromBits, singlePrecType)))
        .isTautological();

    float negInfFromBits = Float.intBitsToFloat(0xff80_0000);
    assertThatFormula(fpmgr.isInfinity(fpmgr.makeNumber(negInfFromBits, singlePrecType)))
        .isTautological();

    float zeroFromBits = Float.intBitsToFloat(0x0000_0000);
    assertThatFormula(fpmgr.isZero(fpmgr.makeNumber(zeroFromBits, singlePrecType)))
        .isTautological();

    float negZeroFromBits = Float.intBitsToFloat(0x8000_0000);
    assertThatFormula(fpmgr.isZero(fpmgr.makeNumber(negZeroFromBits, singlePrecType)))
        .isTautological();

    for (float nanFromBits :
        new float[] {
          Float.intBitsToFloat(0x7fc0_0001),
          Float.intBitsToFloat(0x7fc0_0002),
          Float.intBitsToFloat(0x7fc0_0003),
          Float.intBitsToFloat(0x7fc1_2345),
          Float.intBitsToFloat(0x7fdf_5678),
          Float.intBitsToFloat(0x7ff0_0001),
          // there are some more combinations for NaN, too much for one small test.
        }) {
      assertThatFormula(fpmgr.isNaN(fpmgr.makeNumber(nanFromBits, singlePrecType)))
          .isTautological();
    }
  }

  @Test
  public void specialValueFunctionsFrom64Bits() throws SolverException, InterruptedException {
    double posInfFromBits = Double.longBitsToDouble(0x7ff0_0000_0000_0000L);
    assertThatFormula(fpmgr.isInfinity(fpmgr.makeNumber(posInfFromBits, doublePrecType)))
        .isTautological();

    double negInfFromBits = Double.longBitsToDouble(0xfff0_0000_0000_0000L);
    assertThatFormula(fpmgr.isInfinity(fpmgr.makeNumber(negInfFromBits, doublePrecType)))
        .isTautological();

    double zeroFromBits = Double.longBitsToDouble(0x0000_0000_0000_0000L);
    assertThatFormula(fpmgr.isZero(fpmgr.makeNumber(zeroFromBits, doublePrecType)))
        .isTautological();

    double negZeroFromBits = Double.longBitsToDouble(0x8000_0000_0000_0000L);
    assertThatFormula(fpmgr.isZero(fpmgr.makeNumber(negZeroFromBits, doublePrecType)))
        .isTautological();

    for (double nanFromBits :
        new double[] {
          Double.longBitsToDouble(0x7ff8_0000_0000_0001L),
          Double.longBitsToDouble(0x7ff8_0000_0000_0002L),
          Double.longBitsToDouble(0x7ff8_0000_0000_0003L),
          Double.longBitsToDouble(0x7ff8_1234_5678_9abcL),
          Double.longBitsToDouble(0x7ffc_9876_5432_1001L),
          Double.longBitsToDouble(0x7fff_ffff_ffff_fff2L),
          // there are some more combinations for NaN, too much for one small test.
        }) {
      assertThatFormula(fpmgr.isNaN(fpmgr.makeNumber(nanFromBits, doublePrecType)))
          .isTautological();
    }
  }

  @Test
  public void specialValueFunctionsFrom32Bits2() throws SolverException, InterruptedException {
    requireBitvectors();
    requireNativeFPToBitvector();

    final FloatingPointFormula x = fpmgr.makeVariable("x32", singlePrecType);
    final BitvectorFormula signBit = bvmgr.extract(fpmgr.toIeeeBitvector(x), 31, 31);
    final BitvectorFormula exponent = bvmgr.extract(fpmgr.toIeeeBitvector(x), 30, 23);
    final BitvectorFormula mantissa = bvmgr.extract(fpmgr.toIeeeBitvector(x), 22, 0);

    assertThatFormula(fpmgr.isInfinity(x))
        .isEquivalentTo(
            bmgr.or(
                bvmgr.equal(fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(32, 0x7f80_0000L)),
                bvmgr.equal(fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(32, 0xff80_0000L))));

    assertThatFormula(fpmgr.isZero(x))
        .isEquivalentTo(
            bmgr.or(
                bvmgr.equal(fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(32, 0x0000_0000)),
                bvmgr.equal(fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(32, 0x8000_0000L))));

    assertThatFormula(fpmgr.isNormal(x))
        .isEquivalentTo(
            bmgr.and(
                bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(8, 0))),
                bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(8, -1)))));

    assertThatFormula(fpmgr.isSubnormal(x))
        .isEquivalentTo(
            bmgr.and(
                bvmgr.equal(exponent, bvmgr.makeBitvector(8, 0)),
                bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(23, 0)))));

    assertThatFormula(fpmgr.isNaN(x))
        .isEquivalentTo(
            bmgr.and(
                bvmgr.equal(exponent, bvmgr.makeBitvector(8, -1)),
                bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(23, 0)))));

    assertThatFormula(fpmgr.isNegative(x))
        .isEquivalentTo(
            bmgr.and(bmgr.not(fpmgr.isNaN(x)), bvmgr.equal(signBit, bvmgr.makeBitvector(1, 1))));
  }

  @Test
  public void specialValueFunctionsFrom64Bits2() throws SolverException, InterruptedException {
    requireBitvectors();
    requireNativeFPToBitvector();

    final FloatingPointFormula x = fpmgr.makeVariable("x64", doublePrecType);
    final BitvectorFormula signBit = bvmgr.extract(fpmgr.toIeeeBitvector(x), 63, 63);
    final BitvectorFormula exponent = bvmgr.extract(fpmgr.toIeeeBitvector(x), 62, 52);
    final BitvectorFormula mantissa = bvmgr.extract(fpmgr.toIeeeBitvector(x), 51, 0);

    assertThatFormula(fpmgr.isInfinity(x))
        .isEquivalentTo(
            bmgr.or(
                bvmgr.equal(
                    fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(64, 0x7ff0_0000_0000_0000L)),
                bvmgr.equal(
                    fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(64, 0xfff0_0000_0000_0000L))));

    assertThatFormula(fpmgr.isZero(x))
        .isEquivalentTo(
            bmgr.or(
                bvmgr.equal(
                    fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(64, 0x0000_0000_0000_0000L)),
                bvmgr.equal(
                    fpmgr.toIeeeBitvector(x), bvmgr.makeBitvector(64, 0x8000_0000_0000_0000L))));

    assertThatFormula(fpmgr.isNormal(x))
        .isEquivalentTo(
            bmgr.and(
                bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(11, 0))),
                bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(11, -1)))));

    assertThatFormula(fpmgr.isSubnormal(x))
        .isEquivalentTo(
            bmgr.and(
                bvmgr.equal(exponent, bvmgr.makeBitvector(11, 0)),
                bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(52, 0)))));

    assertThatFormula(fpmgr.isNaN(x))
        .isEquivalentTo(
            bmgr.and(
                bvmgr.equal(exponent, bvmgr.makeBitvector(11, -1)),
                bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(52, 0)))));

    assertThatFormula(fpmgr.isNegative(x))
        .isEquivalentTo(
            bmgr.and(bmgr.not(fpmgr.isNaN(x)), bvmgr.equal(signBit, bvmgr.makeBitvector(1, 1))));
  }

  // Same as specialValueFunctionsFrom32Bits2, but with fallback toIeeeBitvector() implementation.
  @Test
  public void specialValueFunctionsFrom32Bits2ToIeeeFallback()
      throws SolverException, InterruptedException {
    requireBitvectors();

    final FloatingPointFormula fpX = fpmgr.makeVariable("x32", singlePrecType);
    final BitvectorFormula bvX = bvmgr.makeVariable(singlePrecType.getTotalSize(), "bvConst_x");
    BooleanFormula fpXToBvConstraint = fpmgr.toIeeeBitvector(fpX, bvX);

    final BitvectorFormula signBit = bvmgr.extract(bvX, 31, 31);
    final BitvectorFormula exponent = bvmgr.extract(bvX, 30, 23);
    final BitvectorFormula mantissa = bvmgr.extract(bvX, 22, 0);

    assertThatFormula(
            bmgr.implication(
                fpXToBvConstraint,
                bmgr.equivalence(
                    fpmgr.isInfinity(fpX),
                    bmgr.or(
                        bvmgr.equal(bvX, bvmgr.makeBitvector(32, 0x7f80_0000L)),
                        bvmgr.equal(bvX, bvmgr.makeBitvector(32, 0xff80_0000L))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                fpXToBvConstraint,
                bmgr.equivalence(
                    fpmgr.isZero(fpX),
                    bmgr.or(
                        bvmgr.equal(bvX, bvmgr.makeBitvector(32, 0x0000_0000)),
                        bvmgr.equal(bvX, bvmgr.makeBitvector(32, 0x8000_0000L))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                fpXToBvConstraint,
                bmgr.equivalence(
                    fpmgr.isNormal(fpX),
                    bmgr.and(
                        bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(8, 0))),
                        bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(8, -1)))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                fpXToBvConstraint,
                bmgr.equivalence(
                    fpmgr.isSubnormal(fpX),
                    bmgr.and(
                        bvmgr.equal(exponent, bvmgr.makeBitvector(8, 0)),
                        bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(23, 0)))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                fpXToBvConstraint,
                bmgr.equivalence(
                    fpmgr.isNaN(fpX),
                    bmgr.and(
                        bvmgr.equal(exponent, bvmgr.makeBitvector(8, -1)),
                        bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(23, 0)))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                fpXToBvConstraint,
                bmgr.equivalence(
                    fpmgr.isNegative(fpX),
                    bmgr.and(
                        bmgr.not(fpmgr.isNaN(fpX)),
                        bvmgr.equal(signBit, bvmgr.makeBitvector(1, 1))))))
        .isTautological();
  }

  // Same as specialValueFunctionsFrom64Bits2, but with fallback toIeeeBitvector() implementation.
  @Test
  public void specialValueFunctionsFrom64Bits2ToIeeeFallback()
      throws SolverException, InterruptedException {
    requireBitvectors();

    final FloatingPointFormula x = fpmgr.makeVariable("x64", doublePrecType);
    final BitvectorFormula xToIeeeBv =
        bvmgr.makeVariable(doublePrecType.getTotalSize(), "bvConst_x");
    BooleanFormula xToIeeeConstraint = fpmgr.toIeeeBitvector(x, xToIeeeBv);

    final BitvectorFormula signBit = bvmgr.extract(xToIeeeBv, 63, 63);
    final BitvectorFormula exponent = bvmgr.extract(xToIeeeBv, 62, 52);
    final BitvectorFormula mantissa = bvmgr.extract(xToIeeeBv, 51, 0);

    assertThatFormula(
            bmgr.implication(
                xToIeeeConstraint,
                bmgr.equivalence(
                    fpmgr.isInfinity(x),
                    bmgr.or(
                        bvmgr.equal(xToIeeeBv, bvmgr.makeBitvector(64, 0x7ff0_0000_0000_0000L)),
                        bvmgr.equal(xToIeeeBv, bvmgr.makeBitvector(64, 0xfff0_0000_0000_0000L))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                xToIeeeConstraint,
                bmgr.equivalence(
                    fpmgr.isZero(x),
                    bmgr.or(
                        bvmgr.equal(xToIeeeBv, bvmgr.makeBitvector(64, 0x0000_0000_0000_0000L)),
                        bvmgr.equal(xToIeeeBv, bvmgr.makeBitvector(64, 0x8000_0000_0000_0000L))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                xToIeeeConstraint,
                bmgr.equivalence(
                    fpmgr.isNormal(x),
                    bmgr.and(
                        bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(11, 0))),
                        bmgr.not(bvmgr.equal(exponent, bvmgr.makeBitvector(11, -1)))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                xToIeeeConstraint,
                bmgr.equivalence(
                    fpmgr.isSubnormal(x),
                    bmgr.and(
                        bvmgr.equal(exponent, bvmgr.makeBitvector(11, 0)),
                        bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(52, 0)))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                xToIeeeConstraint,
                bmgr.equivalence(
                    fpmgr.isNaN(x),
                    bmgr.and(
                        bvmgr.equal(exponent, bvmgr.makeBitvector(11, -1)),
                        bmgr.not(bvmgr.equal(mantissa, bvmgr.makeBitvector(52, 0)))))))
        .isTautological();

    assertThatFormula(
            bmgr.implication(
                xToIeeeConstraint,
                bmgr.equivalence(
                    fpmgr.isNegative(x),
                    bmgr.and(
                        bmgr.not(fpmgr.isNaN(x)),
                        bvmgr.equal(signBit, bvmgr.makeBitvector(1, 1))))))
        .isTautological();
  }

  // Tests +-0 and +-Infinity from BV -> FP
  @Test
  public void floatingPointSpecialNumberFromBitvector32()
      throws SolverException, InterruptedException {

    ImmutableMap<String, String> fpSpecialNumBvsAndNames =
        ImmutableMap.of(
            SINGLE_PRECISION_POSITIVE_ZERO_BITWISE,
            "+0.0",
            SINGLE_PRECISION_NEGATIVE_ZERO_BITWISE,
            "-0.0",
            SINGLE_PRECISION_POSITIVE_INFINITY_BITWISE,
            "+Infinity",
            SINGLE_PRECISION_NEGATIVE_INFINITY_BITWISE,
            "-Infinity");

    for (Entry<String, String> fpSpecialNumBvAndName : fpSpecialNumBvsAndNames.entrySet()) {
      String specialFpNumAsBv = fpSpecialNumBvAndName.getKey();
      String stringRepresentation = fpSpecialNumBvAndName.getValue();

      final BitvectorFormula bv =
          bvmgr.makeBitvector(
              singlePrecType.getTotalSize(), BigInteger.valueOf(Long.valueOf(specialFpNumAsBv, 2)));
      final FloatingPointFormula fpFromBv = fpmgr.makeVariable("fpFromBv", singlePrecType);
      final FloatingPointFormula someFP = fpmgr.makeVariable("someFPNumber", singlePrecType);
      // toIeeeBitvector(FloatingPointFormula, BitvectorFormula) is built from fromIeeeBitvector()!
      BooleanFormula bvToIeeeFPConstraint = fpmgr.toIeeeBitvector(fpFromBv, bv);

      BooleanFormula fpFromBvIsNotNan = bmgr.not(fpmgr.isNaN(fpFromBv));
      assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpFromBvIsNotNan)).isTautological();

      BooleanFormula fpFromBvIsNotEqualNaN =
          bmgr.not(fpmgr.equalWithFPSemantics(fpmgr.makeNaN(singlePrecType), fpFromBv));
      assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpFromBvIsNotEqualNaN))
          .isTautological();

      BooleanFormula fpFromBvIsEqualItself = fpmgr.equalWithFPSemantics(fpFromBv, fpFromBv);
      assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpFromBvIsEqualItself))
          .isTautological();

      if (stringRepresentation.contains("0")) {
        assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpmgr.isZero(fpFromBv)))
            .isTautological();
      } else {
        assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpmgr.isInfinity(fpFromBv)))
            .isTautological();
      }

      for (String specialFpNum : ImmutableSet.of("+0.0", "-0.0", "+Infinity", "-Infinity")) {
        BooleanFormula fpFromBvIsEqualSpecialNum =
            fpmgr.equalWithFPSemantics(fpmgr.makeNumber(specialFpNum, singlePrecType), fpFromBv);
        if (stringRepresentation.contains("0") && specialFpNum.contains("0")) {
          // All zero equality is always true (i.e. they ignore the sign bit)
          assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpFromBvIsEqualSpecialNum))
              .isTautological();
        } else if (stringRepresentation.equals(specialFpNum)) {
          // Infinity equality takes the sign bit into account
          assertThatFormula(bmgr.implication(bvToIeeeFPConstraint, fpFromBvIsEqualSpecialNum))
              .isTautological();
        } else {
          assertThatFormula(bmgr.and(bvToIeeeFPConstraint, fpFromBvIsEqualSpecialNum))
              .isUnsatisfiable();
        }
      }

      try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        prover.push(bvToIeeeFPConstraint); // has to be true!
        prover.push(fpmgr.equalWithFPSemantics(someFP, fpFromBv));
        assertThat(prover).isSatisfiable();

        try (Model model = prover.getModel()) {
          FloatingPointNumber fpValue = model.evaluate(someFP);
          String fpAsString = fpValue.toString();

          // 0.0 and -0.0 are equal for FP equality, hence a solver might return any
          switch (solver) {
            case Z3:
            case Z3_WITH_INTERPOLATION:
              if (specialFpNumAsBv.equals(SINGLE_PRECISION_POSITIVE_ZERO_BITWISE)) {
                assertThat(fpAsString).isEqualTo(SINGLE_PRECISION_NEGATIVE_ZERO_BITWISE);
                break;
              }
              //$FALL-THROUGH$
            case MATHSAT5:
              if (specialFpNumAsBv.equals(SINGLE_PRECISION_NEGATIVE_ZERO_BITWISE)) {
                assertThat(fpAsString).isEqualTo(SINGLE_PRECISION_POSITIVE_ZERO_BITWISE);
                break;
              }
              //$FALL-THROUGH$
            default:
              assertThat(fpAsString).isEqualTo(specialFpNumAsBv);
          }
        }
      }
    }
  }

  // Test that multiple FP NaNs built from bitvectors compare to NaN in SMT FP theory and their
  // values and that a solver always just returns a single NaN bitwise representation per default
  @Test
  public void toIeeeBitvectorFallbackEqualityWithDistinctNaN32()
      throws SolverException, InterruptedException {
    requireBitvectors();

    // Solvers transform arbitrary input NaNs into a single NaN representation
    String defaultNaN = null;

    for (String nanString : SINGLE_PRECISION_NANS_BITWISE) {
      final BitvectorFormula bvNaN =
          bvmgr.makeBitvector(
              singlePrecType.getTotalSize(), BigInteger.valueOf(Long.valueOf(nanString, 2)));
      final FloatingPointFormula fpFromBv = fpmgr.makeVariable("bvNaN", singlePrecType);
      // toIeeeBitvector(FloatingPointFormula, BitvectorFormula) is built from fromIeeeBitvector()
      BooleanFormula xToIeeeConstraint = fpmgr.toIeeeBitvector(fpFromBv, bvNaN);

      BooleanFormula fpFromBvIsNan = fpmgr.isNaN(fpFromBv);
      BooleanFormula fpFromBvIsNotEqualNaN =
          bmgr.not(fpmgr.equalWithFPSemantics(fpmgr.makeNaN(singlePrecType), fpFromBv));
      BooleanFormula fpFromBvIsNotEqualItself =
          bmgr.not(fpmgr.equalWithFPSemantics(fpFromBv, fpFromBv));
      BooleanFormula assertion =
          bmgr.implication(
              xToIeeeConstraint,
              bmgr.and(fpFromBvIsNan, fpFromBvIsNotEqualNaN, fpFromBvIsNotEqualItself));

      assertThatFormula(assertion).isTautological();

      try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        prover.push(xToIeeeConstraint); // xToIeeeConstraint has to be true!
        prover.push(assertion);
        assertThat(prover).isSatisfiable();

        try (Model model = prover.getModel()) {
          BigInteger bvAsBigInt = model.evaluate(bvNaN);
          // toBinaryString() is not returning the sign bit if its 0, so we need to add it
          String bvAsBvString = Long.toBinaryString(model.evaluate(bvNaN).longValueExact());
          if (bvAsBvString.length() != singlePrecType.getTotalSize()) {
            if (bvAsBigInt.signum() >= 0) {
              bvAsBvString = "0" + bvAsBvString;
            }
          }

          // The used bitvector is really a (known) NaN
          assertThat(bvAsBvString).isIn(SINGLE_PRECISION_NANS_BITWISE);

          FloatingPointNumber fpNanValue = model.evaluate(fpFromBv);
          // The FP is also a (known) NaN
          String fpNanAsString = fpNanValue.toString();
          assertThat(fpNanAsString).isIn(SINGLE_PRECISION_NANS_BITWISE);
          if (defaultNaN == null) {
            defaultNaN = fpNanAsString;
          } else {
            assertThat(fpNanAsString).isEqualTo(defaultNaN);
          }
        }
      }
    }
  }

  @Test
  public void toIeeeBitvectorFallbackEqualityWithNaN32()
      throws SolverException, InterruptedException {
    requireBitvectors();

    for (String nanString : SINGLE_PRECISION_NANS_BITWISE) {
      final BitvectorFormula bvNaN =
          bvmgr.makeBitvector(
              singlePrecType.getTotalSize(), BigInteger.valueOf(Long.valueOf(nanString, 2)));
      final FloatingPointFormula fpFromBv = fpmgr.makeVariable("fp_from_bv", singlePrecType);
      BooleanFormula xToIeeeConstraint = fpmgr.toIeeeBitvector(fpFromBv, bvNaN);

      BooleanFormula fpFromBvIsEqualNaN =
          fpmgr.equalWithFPSemantics(fpmgr.makeNaN(singlePrecType), fpFromBv);
      BooleanFormula fpFromBvIsEqualItself = fpmgr.equalWithFPSemantics(fpFromBv, fpFromBv);

      assertThatFormula(bmgr.implication(xToIeeeConstraint, bmgr.not(fpFromBvIsEqualNaN)))
          .isTautological();
      assertThatFormula(bmgr.implication(xToIeeeConstraint, bmgr.not(fpFromBvIsEqualItself)))
          .isTautological();
    }
  }

  @Test
  public void fromIeeeBitvectorEqualityWithNaN32() throws SolverException, InterruptedException {
    requireBitvectors();

    for (String nanString : SINGLE_PRECISION_NANS_BITWISE) {
      final BitvectorFormula bvNaN =
          bvmgr.makeBitvector(
              singlePrecType.getTotalSize(), BigInteger.valueOf(Long.valueOf(nanString, 2)));
      final FloatingPointFormula fpFromBv = fpmgr.fromIeeeBitvector(bvNaN, singlePrecType);

      BooleanFormula fpFromBvIsEqualNaN =
          fpmgr.equalWithFPSemantics(fpmgr.makeNaN(singlePrecType), fpFromBv);
      BooleanFormula fpFromBvIsEqualItself = fpmgr.equalWithFPSemantics(fpFromBv, fpFromBv);

      assertThatFormula(bmgr.not(fpFromBvIsEqualNaN)).isTautological();
      assertThatFormula(bmgr.not(fpFromBvIsEqualItself)).isTautological();
    }
  }

  // Tests FP NaN to bitvector representations
  @Test
  public void toIeeeBitvectorNaNRepresentation32() throws SolverException, InterruptedException {
    requireBitvectors();

    final BitvectorFormula bvNaN = bvmgr.makeVariable(singlePrecType.getTotalSize(), "bvNaN");

    final FloatingPointFormula fpNan = fpmgr.makeNaN(singlePrecType);
    BooleanFormula xToIeeeConstraint = fpmgr.toIeeeBitvector(fpNan, bvNaN);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(xToIeeeConstraint);
      assertThat(prover).isSatisfiable();

      try (Model model = prover.getModel()) {
        BigInteger bvNaNAsBigInt = model.evaluate(bvNaN);
        // toBinaryString() is not returning the sign bit if its 0, so we need to add it
        String bvAsBvString = Long.toBinaryString(model.evaluate(bvNaN).longValueExact());
        if (bvAsBvString.length() != singlePrecType.getTotalSize()) {
          if (bvNaNAsBigInt.signum() >= 0) {
            bvAsBvString = "0" + bvAsBvString;
          }
        }

        // The bitvector is really a (known) NaN
        assertThat(bvAsBvString).isIn(SINGLE_PRECISION_NANS_BITWISE);

        FloatingPointNumber fpNanValue = model.evaluate(fpNan);
        // The FP is also a (known) NaN
        String fpNanAsString = fpNanValue.toString();
        assertThat(fpNanAsString).isIn(SINGLE_PRECISION_NANS_BITWISE);

        // No solver uses the same bit representation for NaN in the FP number and bitvector
        assertThat(fpNanAsString).isNotEqualTo(bvAsBvString);
      }
    }
  }

  // Tests toIeeeBitvector() fallback == toIeeeBitvector() solver native for special numbers,
  // some example numbers, and a variable for single FP precision type
  @Test
  public void floatingPointSinglePrecToIeeeBitvectorFallbackCompareWithNativeTest()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireNativeFPToBitvector();

    FloatingPointType fpType = singlePrecType;
    FloatingPointFormula varSingle = fpmgr.makeVariable("varSingle", fpType);
    Set<FloatingPointFormula> testSetOfFps =
        ImmutableSet.of(nan, posInf, negInf, zero, negZero, one, varSingle);

    int fpTypeSize = fpType.getTotalSize();
    int i = 0;
    for (FloatingPointFormula fpToTest : testSetOfFps) {
      BitvectorFormula fallbackBv = bvmgr.makeVariable(fpTypeSize, "bv" + i++);
      assertThat(bvmgr.getLength(fallbackBv)).isEqualTo(fpTypeSize);
      BooleanFormula fpEqFallbackBv = fpmgr.toIeeeBitvector(fpToTest, fallbackBv);

      BitvectorFormula nativeBv = fpmgr.toIeeeBitvector(fpToTest);
      assertThat(bvmgr.getLength(nativeBv)).isEqualTo(fpTypeSize);

      BooleanFormula constraints = bmgr.and(fpEqFallbackBv, bvmgr.equal(nativeBv, fallbackBv));

      assertThatFormula(constraints).isSatisfiable();
    }
  }

  // Tests toIeeeBitvector() fallback == toIeeeBitvector() solver native for special numbers,
  // some example numbers, and a variable for double FP precision type
  @Test
  public void floatingPointDoublePrecToIeeeBitvectorFallbackCompareWithNativeTest()
      throws SolverException, InterruptedException {
    requireBitvectors();
    requireNativeFPToBitvector();

    FloatingPointType fpType = doublePrecType;
    FloatingPointFormula varDouble = fpmgr.makeVariable("varDouble", fpType);
    Set<FloatingPointFormula> testSetOfFps =
        ImmutableSet.of(
            fpmgr.makeNaN(fpType),
            fpmgr.makePlusInfinity(fpType),
            fpmgr.makeMinusInfinity(fpType),
            fpmgr.makeNumber(0.0, fpType),
            fpmgr.makeNumber(-0.0, fpType),
            fpmgr.makeNumber(1.0, fpType),
            varDouble);

    int fpTypeSize = fpType.getTotalSize();
    int i = 0;
    for (FloatingPointFormula fpToTest : testSetOfFps) {
      BitvectorFormula fallbackBv = bvmgr.makeVariable(fpTypeSize, "bv" + i++);
      assertThat(bvmgr.getLength(fallbackBv)).isEqualTo(fpTypeSize);
      BooleanFormula fpEqFallbackBv = fpmgr.toIeeeBitvector(fpToTest, fallbackBv);

      BitvectorFormula nativeBv = fpmgr.toIeeeBitvector(fpToTest);
      assertThat(bvmgr.getLength(nativeBv)).isEqualTo(fpTypeSize);

      BooleanFormula constraints = bmgr.and(fpEqFallbackBv, bvmgr.equal(nativeBv, fallbackBv));

      assertThatFormula(constraints).isSatisfiable();
    }
  }

  @Test
  public void specialDoubles() throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.assignment(fpmgr.makeNumber(Double.NaN, singlePrecType), nan))
        .isTautological();
    assertThatFormula(
            fpmgr.assignment(fpmgr.makeNumber(Double.POSITIVE_INFINITY, singlePrecType), posInf))
        .isTautological();
    assertThatFormula(
            fpmgr.assignment(fpmgr.makeNumber(Double.NEGATIVE_INFINITY, singlePrecType), negInf))
        .isTautological();
  }

  private void checkEqualityOfNumberConstantsFor(double value, FloatingPointType type)
      throws SolverException, InterruptedException {
    FloatingPointFormula doubleNumber = fpmgr.makeNumber(value, type);
    FloatingPointFormula stringNumber = fpmgr.makeNumber(Double.toString(value), type);
    FloatingPointFormula bigDecimalNumber = fpmgr.makeNumber(BigDecimal.valueOf(value), type);
    FloatingPointFormula rationalNumber =
        fpmgr.makeNumber(Rational.ofBigDecimal(BigDecimal.valueOf(value)), type);

    BooleanFormula eq1 = fpmgr.equalWithFPSemantics(doubleNumber, stringNumber);
    BooleanFormula eq2 = fpmgr.equalWithFPSemantics(doubleNumber, bigDecimalNumber);

    BooleanFormula eq3 = fpmgr.equalWithFPSemantics(doubleNumber, rationalNumber);
    assertThatFormula(bmgr.and(eq1, eq2, eq3)).isTautological();
  }

  @Test
  @SuppressWarnings("FloatingPointLiteralPrecision")
  public void numberConstants() throws SolverException, InterruptedException {
    checkEqualityOfNumberConstantsFor(1.0, singlePrecType);
    checkEqualityOfNumberConstantsFor(-5.877471754111438E-39, singlePrecType);
    checkEqualityOfNumberConstantsFor(-5.877471754111438E-39, doublePrecType);
    checkEqualityOfNumberConstantsFor(3.4028234663852886e+38, singlePrecType);
    checkEqualityOfNumberConstantsFor(3.4028234663852886e+38, doublePrecType);

    // check unequality for large types
    FloatingPointType nearDouble = getFloatingPointTypeFromSizesWithoutHiddenBit(12, 52);
    FloatingPointFormula h1 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(309).multiply(BigDecimal.valueOf(1.0001)), nearDouble);
    FloatingPointFormula h2 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(309).multiply(BigDecimal.valueOf(1.0002)), nearDouble);
    assertThatFormula(fpmgr.equalWithFPSemantics(h1, h2)).isUnsatisfiable();

    // check equality for short types
    FloatingPointType smallType = getFloatingPointTypeFromSizesWithoutHiddenBit(4, 4);
    FloatingPointFormula i1 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.001)), smallType);
    FloatingPointFormula i2 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.002)), smallType);
    FloatingPointFormula inf = fpmgr.makePlusInfinity(smallType);
    assertEqualsAsFp(i1, i2);
    assertEqualsAsFp(i1, inf);
    assertEqualsAsFp(i2, inf);
    assertThatFormula(fpmgr.isInfinity(i1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(i2)).isTautological();

    // and some negative numbers
    FloatingPointFormula ni1 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.001)).negate(), smallType);
    FloatingPointFormula ni2 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.002)).negate(), smallType);
    FloatingPointFormula ninf = fpmgr.makeMinusInfinity(smallType);
    assertEqualsAsFp(ni1, ni2);
    assertEqualsAsFp(ni1, ninf);
    assertEqualsAsFp(ni2, ninf);
    assertThatFormula(fpmgr.isInfinity(ni1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(ni2)).isTautological();
    assertThatFormula(fpmgr.isNegative(ni1)).isTautological();
    assertThatFormula(fpmgr.isNegative(ni2)).isTautological();

    // check equality for short types
    FloatingPointType smallType2 = getFloatingPointTypeFromSizesWithoutHiddenBit(4, 4);
    FloatingPointFormula j1 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.001)), smallType2);
    FloatingPointFormula j2 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.002)), smallType2);
    FloatingPointFormula jnf = fpmgr.makePlusInfinity(smallType);
    assertEqualsAsFp(j1, j2);
    assertEqualsAsFp(j1, jnf);
    assertEqualsAsFp(j2, jnf);
    assertThatFormula(fpmgr.isInfinity(j1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(j2)).isTautological();

    // and some negative numbers
    FloatingPointFormula nj1 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.001)).negate(), smallType2);
    FloatingPointFormula nj2 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.002)).negate(), smallType2);
    FloatingPointFormula njnf = fpmgr.makeMinusInfinity(smallType);
    assertEqualsAsFp(nj1, nj2);
    assertEqualsAsFp(nj1, njnf);
    assertEqualsAsFp(nj2, njnf);
    assertThatFormula(fpmgr.isInfinity(nj1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(nj2)).isTautological();
    assertThatFormula(fpmgr.isNegative(nj1)).isTautological();
    assertThatFormula(fpmgr.isNegative(nj2)).isTautological();

    // Z3 supports at least FloatingPointType(15, 112). Larger types seem to be rounded.
    if (!ImmutableSet.of(Solvers.Z3, Solvers.Z3_WITH_INTERPOLATION, Solvers.CVC4)
        .contains(solver)) {
      // check unequality for very large types
      int exponentSize = solver == Solvers.BITWUZLA ? 30 : 100; // Bitwuzla has issues above 40 bit.
      FloatingPointType largeType =
          getFloatingPointTypeFromSizesWithoutHiddenBit(exponentSize, 100);
      FloatingPointFormula k1 =
          fpmgr.makeNumber(BigDecimal.TEN.pow(200).multiply(BigDecimal.valueOf(1.001)), largeType);
      FloatingPointFormula k2 =
          fpmgr.makeNumber(BigDecimal.TEN.pow(200).multiply(BigDecimal.valueOf(1.002)), largeType);
      assertThatFormula(fpmgr.equalWithFPSemantics(k1, k2)).isUnsatisfiable();
    }
  }

  @Test
  public void numberConstantsNearInf() throws SolverException, InterruptedException {
    checkNearInf(4, 4, 252); // 2**(2**(4-1)) - max(0,2**(2**(4-1)-2-4))
    checkNearInf(5, 4, 254); // 2**(2**(4-1)) - max(0,2**(2**(4-1)-2-5))
    checkNearInf(6, 4, 255); // 2**(2**(4-1)) - max(0,2**(2**(4-1)-2-6))
    checkNearInf(7, 4, 256); // 2**(2**(4-1)) - max(0,?)
    checkNearInf(10, 4, 256); // 2**(2**(4-1)) - max(0,?)

    if (Solvers.CVC4 != solverToUse()) {
      // It seems as if CVC4/symfpu can not handle numbers with size of mantissa < exponent
      // TODO check this!
      checkNearInf(4, 5, 64512); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-4))
      checkNearInf(4, 6, 4227858432L); // 2**(2**(6-1)) - max(0,2**(2**(6-1)-2-4))
    }

    checkNearInf(5, 5, 65024); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-5))
    checkNearInf(6, 5, 65280); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-6))
    checkNearInf(7, 5, 65408); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-7))
    checkNearInf(10, 5, 65520); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-10))
    checkNearInf(14, 5, 65535); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-14))
    checkNearInf(15, 5, 65536); // 2**(2**(5-1)) - max(0,?)

    checkNearInf(10, 6, 4293918720L); // 2**(2**(6-1)) - max(0,2**(2**(6-1)-2-10))
    checkNearInf(16, 6, 4294950912L); // 2**(2**(6-1)) - max(0,2**(2**(6-1)-2-16))
  }

  private void checkNearInf(int mantissa, int exponent, long value)
      throws SolverException, InterruptedException {
    FloatingPointType type = getFloatingPointTypeFromSizesWithoutHiddenBit(exponent, mantissa);
    FloatingPointFormula fp1 = fpmgr.makeNumber(BigDecimal.valueOf(value), type);
    assertThatFormula(fpmgr.isInfinity(fp1)).isTautological();
    FloatingPointFormula fp2 = fpmgr.makeNumber(BigDecimal.valueOf(value - 1), type);
    assertThatFormula(fpmgr.isInfinity(fp2)).isUnsatisfiable();
  }

  @Test
  public void numberConstantsNearMinusInf() throws SolverException, InterruptedException {
    checkNearMinusInf(4, 4, -252);
    checkNearMinusInf(5, 4, -254);
    checkNearMinusInf(6, 4, -255);
    checkNearMinusInf(7, 4, -256);
    checkNearMinusInf(10, 4, -256);

    if (Solvers.CVC4 != solverToUse()) {
      // It seems as if CVC4/symfpu can not handle numbers with size of mantissa < exponent
      // TODO check this!
      checkNearMinusInf(4, 5, -64512);
      checkNearMinusInf(4, 6, -4227858432L);
    }

    checkNearMinusInf(5, 5, -65024);
    checkNearMinusInf(6, 5, -65280);
    checkNearMinusInf(7, 5, -65408);
    checkNearMinusInf(10, 5, -65520);
    checkNearMinusInf(14, 5, -65535);
    checkNearMinusInf(15, 5, -65536);

    checkNearMinusInf(10, 6, -4293918720L);
    checkNearMinusInf(16, 6, -4294950912L);
  }

  private void checkNearMinusInf(int mantissa, int exponent, long value)
      throws SolverException, InterruptedException {
    FloatingPointType type = getFloatingPointTypeFromSizesWithoutHiddenBit(exponent, mantissa);
    FloatingPointFormula fp1 = fpmgr.makeNumber(BigDecimal.valueOf(value), type);
    assertThatFormula(fpmgr.isInfinity(fp1)).isTautological();
    FloatingPointFormula fp2 = fpmgr.makeNumber(BigDecimal.valueOf(value + 1), type);
    assertThatFormula(fpmgr.isInfinity(fp2)).isUnsatisfiable();
  }

  @Test
  @SuppressWarnings("FloatingPointLiteralPrecision")
  public void cast() throws SolverException, InterruptedException {
    FloatingPointFormula doublePrecNumber = fpmgr.makeNumber(1.5, doublePrecType);
    FloatingPointFormula singlePrecNumber = fpmgr.makeNumber(1.5, singlePrecType);

    FloatingPointFormula narrowedNumber = fpmgr.castTo(doublePrecNumber, true, singlePrecType);
    FloatingPointFormula widenedNumber = fpmgr.castTo(singlePrecNumber, true, doublePrecType);

    assertEqualsAsFp(narrowedNumber, singlePrecNumber);
    assertEqualsAsFp(widenedNumber, doublePrecNumber);

    FloatingPointFormula doublePrecSmallNumber =
        fpmgr.makeNumber(5.877471754111438E-39, doublePrecType);
    FloatingPointFormula singlePrecSmallNumber =
        fpmgr.makeNumber(5.877471754111438E-39, singlePrecType);
    FloatingPointFormula widenedSmallNumber =
        fpmgr.castTo(singlePrecSmallNumber, true, doublePrecType);
    assertEqualsAsFp(widenedSmallNumber, doublePrecSmallNumber);
  }

  @Test
  public void bvToFpSinglePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      bvToFp(i, singlePrecType);
    }
  }

  @Test
  public void bvToFpDoublePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      bvToFp(i, doublePrecType);
    }
  }

  private void bvToFp(int i, FloatingPointType prec) throws SolverException, InterruptedException {
    BitvectorFormula bv = bvmgr.makeBitvector(32, i);
    FloatingPointFormula fp = fpmgr.makeNumber(i, prec);

    FloatingPointFormula signedBvToFp = fpmgr.castFrom(bv, true, prec);
    FloatingPointFormula unsignedBvToFp = fpmgr.castFrom(bv, false, prec);

    assertEqualsAsFp(fp, signedBvToFp);
    assertEqualsAsFp(fp, unsignedBvToFp);
  }

  /** check whether rounded input is equal to result with rounding-mode. */
  private void round0(
      double value, double toZero, double pos, double neg, double tiesEven, double tiesAway)
      throws SolverException, InterruptedException {
    FloatingPointFormula f = fpmgr.makeNumber(value, singlePrecType);

    // check types
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.TOWARD_ZERO)))
        .isEqualTo(singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.TOWARD_POSITIVE)))
        .isEqualTo(singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.TOWARD_NEGATIVE)))
        .isEqualTo(singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN)))
        .isEqualTo(singlePrecType);
    if (solver != Solvers.MATHSAT5) { // Mathsat does not support NEAREST_TIES_AWAY
      assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_AWAY)))
          .isEqualTo(singlePrecType);
    }

    // check values
    assertEqualsAsFp(
        fpmgr.makeNumber(toZero, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_ZERO));

    assertEqualsAsFp(
        fpmgr.makeNumber(pos, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_POSITIVE));

    assertEqualsAsFp(
        fpmgr.makeNumber(neg, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_NEGATIVE));

    assertEqualsAsFp(
        fpmgr.makeNumber(tiesEven, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN));

    if (solver != Solvers.MATHSAT5) { // Mathsat does not support NEAREST_TIES_AWAY
      assertEqualsAsFp(
          fpmgr.makeNumber(tiesAway, singlePrecType),
          fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_AWAY));
    }
  }

  private void assertEqualsAsFp(FloatingPointFormula f1, FloatingPointFormula f2)
      throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.equalWithFPSemantics(f1, f2)).isTautological();
  }

  private void assertEqualsAsFormula(FloatingPointFormula f1, FloatingPointFormula f2)
      throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.assignment(f1, f2)).isTautological();
  }

  @Test
  public void roundingModeMapping() {
    for (FloatingPointRoundingMode rm : FloatingPointRoundingMode.values()) {
      if (solver == Solvers.MATHSAT5 && rm == FloatingPointRoundingMode.NEAREST_TIES_AWAY) {
        // SKIP MathSAT does not support rounding mode "nearest-ties-away"
        continue;
      }
      assertThat(fpmgr.fromRoundingModeFormula(fpmgr.makeRoundingMode(rm))).isEqualTo(rm);
    }
  }

  @Test
  public void round() throws SolverException, InterruptedException {
    requireIntegers();

    // constants
    round0(0, 0, 0, 0, 0, 0);
    round0(1, 1, 1, 1, 1, 1);
    round0(-1, -1, -1, -1, -1, -1);

    // positive odd
    round0(1.1, 1, 2, 1, 1, 1);
    round0(1.5, 1, 2, 1, 2, 2);
    round0(1.9, 1, 2, 1, 2, 2);

    // positive even
    round0(10.1, 10, 11, 10, 10, 10);
    round0(10.5, 10, 11, 10, 10, 11);
    round0(10.9, 10, 11, 10, 11, 11);

    // negative odd
    round0(-1.1, -1, -1, -2, -1, -1);
    round0(-1.5, -1, -1, -2, -2, -2);
    round0(-1.9, -1, -1, -2, -2, -2);

    // negative even
    round0(-10.1, -10, -10, -11, -10, -10);
    round0(-10.5, -10, -10, -11, -10, -11);
    round0(-10.9, -10, -10, -11, -11, -11);
  }

  @Test
  public void bvToFpMinusOne() throws SolverException, InterruptedException {
    requireBitvectors();

    BitvectorFormula bvOne = bvmgr.makeBitvector(32, -1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    // A 32bit value "-1" when interpreted as unsigned is 2^31 - 1
    FloatingPointFormula fpMinInt = fpmgr.makeNumber(Math.pow(2, 32) - 1, singlePrecType);

    FloatingPointFormula unsignedBvToFpOne = fpmgr.castFrom(bvOne, false, singlePrecType);
    FloatingPointFormula signedBvToFpOne = fpmgr.castFrom(bvOne, true, singlePrecType);

    assertEqualsAsFp(fpOne, signedBvToFpOne);
    assertEqualsAsFp(fpMinInt, unsignedBvToFpOne);
  }

  @Test
  public void fpToBvSimpleNumbersSinglePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(i, singlePrecType);
    }
  }

  @Test
  public void fpToBvSimpleNegativeNumbersSinglePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(-i, singlePrecType);
    }
  }

  @Test
  public void fpToBvSimpleNumbersDoublePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(i, doublePrecType);
    }
  }

  @Test
  public void fpToBvSimpleNegativeNumbersDoublePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(-i, doublePrecType);
    }
  }

  private void fpToBv(int i, FloatingPointType prec) throws SolverException, InterruptedException {
    BitvectorFormula bv = bvmgr.makeBitvector(prec.getTotalSize(), i);
    FloatingPointFormula fp = fpmgr.makeNumber(i, prec);

    BitvectorFormula fpToBv =
        fpmgr.castTo(fp, true, FormulaType.getBitvectorTypeWithSize(prec.getTotalSize()));
    assertThatFormula(bvmgr.equal(bv, fpToBv)).isTautological();
  }

  @Test
  public void rationalToFpOne() throws SolverException, InterruptedException {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    FloatingPointFormula ratToFpOne = fpmgr.castFrom(ratOne, true, singlePrecType);
    FloatingPointFormula unsignedRatToFpOne = fpmgr.castFrom(ratOne, false, singlePrecType);
    assertThat(unsignedRatToFpOne).isEqualTo(ratToFpOne);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, ratToFpOne)).isSatisfiable();
  }

  @Test
  public void rationalToFpMinusOne() throws SolverException, InterruptedException {
    requireRationals();
    requireBitvectors();

    NumeralFormula ratOne = rmgr.makeNumber(-1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    FloatingPointFormula ratToFpOne = fpmgr.castFrom(ratOne, true, singlePrecType);
    FloatingPointFormula unsignedRatToFpOne = fpmgr.castFrom(ratOne, false, singlePrecType);
    assertThat(unsignedRatToFpOne).isEqualTo(ratToFpOne);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, ratToFpOne)).isSatisfiable();
  }

  @Test
  public void fpToRationalOne() throws SolverException, InterruptedException {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    NumeralFormula fpToRatOne = fpmgr.castTo(fpOne, true, FormulaType.RationalType);

    assertThatFormula(rmgr.equal(ratOne, fpToRatOne)).isSatisfiable();
  }

  @Test
  public void fpToRationalMinusOne() throws SolverException, InterruptedException {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(-1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    NumeralFormula fpToRatOne = fpmgr.castTo(fpOne, true, FormulaType.RationalType);

    assertThatFormula(rmgr.equal(ratOne, fpToRatOne)).isSatisfiable();
  }

  @Test
  public void fpTraversal() {
    assertThat(mgr.extractVariables(zero)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(zero)).isEmpty();

    assertThat(mgr.extractVariables(one)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(one)).isEmpty();

    assertThat(mgr.extractVariables(posInf)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(posInf)).isEmpty();

    assertThat(mgr.extractVariables(nan)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(nan)).isEmpty();

    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    assertThat(mgr.extractVariables(var)).containsExactly("x", var);
    assertThat(mgr.extractVariablesAndUFs(var)).containsExactly("x", var);
  }

  @Test
  public void fpTraversalWithRoundingMode() {
    FloatingPointFormula two = fpmgr.makeNumber(2.0, singlePrecType);
    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    FloatingPointFormula mult = fpmgr.multiply(two, var);
    assertThat(mgr.extractVariables(mult)).containsExactly("x", var);
    assertThat(mgr.extractVariablesAndUFs(mult)).containsExactly("x", var);
  }

  @Test
  public void fpIeeeConversionTypes() {
    requireNativeFPToBitvector();

    FloatingPointFormula var = fpmgr.makeVariable("var", singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.toIeeeBitvector(var)))
        .isEqualTo(FormulaType.getBitvectorTypeWithSize(32));
  }

  @Test
  public void fpIeeeConversion() throws SolverException, InterruptedException {
    requireNativeFPToBitvector();

    FloatingPointFormula var = fpmgr.makeVariable("var", singlePrecType);
    assertThatFormula(
            fpmgr.assignment(
                var, fpmgr.fromIeeeBitvector(fpmgr.toIeeeBitvector(var), singlePrecType)))
        .isTautological();
  }

  @Test
  public void ieeeFpConversion() throws SolverException, InterruptedException {
    requireNativeFPToBitvector();

    BitvectorFormula var = bvmgr.makeBitvector(32, 123456789);
    assertThatFormula(
            bvmgr.equal(var, fpmgr.toIeeeBitvector(fpmgr.fromIeeeBitvector(var, singlePrecType))))
        .isTautological();
  }

  /**
   * Map the function over the input list and prove the returned assertions.
   *
   * @param args A list of arguments to the function
   * @param f A function that takes values from the list and returns assertions
   */
  private <T> void proveForAll(List<T> args, Function<T, BooleanFormula> f)
      throws InterruptedException, SolverException {
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      for (T value : args) {
        prover.addConstraint(f.apply(value));
        assertThat(prover).isSatisfiable();
      }
    }
  }

  @Test
  public void checkString2FpConversion32() throws SolverException, InterruptedException {
    proveForAll(
        getListOfFloats(),
        pFloat ->
            fpmgr.equalWithFPSemantics(
                fpmgr.makeNumber(pFloat, singlePrecType),
                fpmgr.makeNumber(Float.toString(pFloat), singlePrecType)));
  }

  @Test
  public void checkString2FpConversion64() throws SolverException, InterruptedException {
    proveForAll(
        getListOfDoubles(),
        pDouble ->
            fpmgr.equalWithFPSemantics(
                fpmgr.makeNumber(pDouble, doublePrecType),
                fpmgr.makeNumber(Double.toString(pDouble), doublePrecType)));
  }

  @Test
  public void checkErrorOnInvalidSize_IeeeBv2FpConversion() {
    BitvectorFormula bv = bvmgr.makeBitvector(9, 123);

    var exSingle =
        assertThrows(
            IllegalArgumentException.class, () -> fpmgr.fromIeeeBitvector(bv, singlePrecType));
    assertThat(exSingle.getMessage())
        .contains(
            "The total size 32 of type FloatingPoint<exp=8,mant=24> "
                + "has to match the size 9 of type Bitvector<9>.");

    var exDouble =
        assertThrows(
            IllegalArgumentException.class, () -> fpmgr.fromIeeeBitvector(bv, doublePrecType));
    assertThat(exDouble.getMessage())
        .contains(
            "The total size 64 of type FloatingPoint<exp=11,mant=53> "
                + "has to match the size 9 of type Bitvector<9>.");
  }

  @Test
  public void checkIeeeBv2FpConversion32() throws SolverException, InterruptedException {
    proveForAll(
        // makeFP(value.float) == fromBV(makeBV(value.bits))
        getListOfFloats(),
        pFloat ->
            fpmgr.equalWithFPSemantics(
                fpmgr.makeNumber(pFloat, singlePrecType),
                fpmgr.fromIeeeBitvector(
                    bvmgr.makeBitvector(32, Float.floatToRawIntBits(pFloat)), singlePrecType)));
  }

  @Test
  public void checkIeeeBv2FpConversion64() throws SolverException, InterruptedException {
    proveForAll(
        // makeFP(value.float) == fromBV(makeBV(value.bits))
        getListOfDoubles(),
        pDouble ->
            fpmgr.equalWithFPSemantics(
                fpmgr.makeNumber(pDouble, doublePrecType),
                fpmgr.fromIeeeBitvector(
                    bvmgr.makeBitvector(64, Double.doubleToRawLongBits(pDouble)), doublePrecType)));
  }

  @Test
  public void checkIeeeFp2BvConversion32() throws SolverException, InterruptedException {
    requireNativeFPToBitvector();

    proveForAll(
        // makeBV(value.bits) == fromFP(makeFP(value.float))
        getListOfFloats(),
        pFloat ->
            bvmgr.equal(
                bvmgr.makeBitvector(32, Float.floatToRawIntBits(pFloat)),
                fpmgr.toIeeeBitvector(fpmgr.makeNumber(pFloat, singlePrecType))));
  }

  @Test
  public void checkIeeeFp2BvConversion64() throws SolverException, InterruptedException {
    requireNativeFPToBitvector();

    proveForAll(
        // makeBV(value.bits) == fromFP(makeFP(value.float))
        getListOfFloats(),
        pDouble ->
            bvmgr.equal(
                bvmgr.makeBitvector(64, Double.doubleToRawLongBits(pDouble)),
                fpmgr.toIeeeBitvector(fpmgr.makeNumber(pDouble, doublePrecType))));
  }

  // Equal to checkIeeeFp2BvConversion32, but with the fallback method of toIeeeBitvector()
  @Test
  public void checkIeeeFp2BvConversion32WithFallback()
      throws SolverException, InterruptedException {
    requireBitvectors();

    proveForAll(
        // makeBV(value.bits) == fromFP(makeFP(value.float))
        getListOfFloats(),
        pFloat -> {
          var bv = bvmgr.makeVariable(32, "bv");
          return bmgr.implication(
              fpmgr.toIeeeBitvector(fpmgr.makeNumber(pFloat, singlePrecType), bv),
              bvmgr.equal(bvmgr.makeBitvector(32, Float.floatToRawIntBits(pFloat)), bv));
        });
  }

  // Equal to checkIeeeFp2BvConversion64, but with the fallback method of toIeeeBitvector()
  @Test
  public void checkIeeeFp2BvConversion64WithFallback()
      throws SolverException, InterruptedException {
    requireBitvectors();

    proveForAll(
        // makeBV(value.bits) == fromFP(makeFP(value.float))
        getListOfFloats(),
        pDouble -> {
          var bv = bvmgr.makeVariable(64, "bv");
          return bmgr.implication(
              fpmgr.toIeeeBitvector(fpmgr.makeNumber(pDouble, doublePrecType), bv),
              bvmgr.equal(bvmgr.makeBitvector(64, Double.doubleToRawLongBits(pDouble)), bv));
        });
  }

  private List<Float> getListOfFloats() {
    List<Float> flts =
        Lists.newArrayList(
            2.139922e-34f, // normal
            8.345803E-39f, // subnormal
            // Float.NaN, // NaN is no unique bitvector
            Float.MIN_NORMAL,
            Float.MIN_VALUE,
            Float.MAX_VALUE,
            Float.POSITIVE_INFINITY,
            Float.NEGATIVE_INFINITY,
            0.0f,
            -0.0f,
            1f,
            -1f,
            2f,
            -2f);

    for (int i = 1; i < 10; i++) {
      for (int j = 1; j < 10; j++) {
        flts.add((float) (i * Math.pow(10, j)));
        flts.add((float) (-i * Math.pow(10, j)));
      }
    }

    Random rand = new Random(0);
    for (int i = 0; i < NUM_RANDOM_TESTS; i++) {
      float flt = Float.intBitsToFloat(rand.nextInt());
      if (!Float.isNaN(flt)) {
        flts.add(flt);
      }
    }

    return flts;
  }

  private List<Double> getListOfDoubles() {
    List<Double> dbls =
        Lists.newArrayList(
            // Double.NaN, // NaN is no unique bitvector
            Double.MIN_NORMAL,
            Double.MIN_VALUE,
            Double.MAX_VALUE,
            Double.POSITIVE_INFINITY,
            Double.NEGATIVE_INFINITY,
            0.0,
            -0.0,
            1d,
            -1d,
            2d,
            -2d);

    for (int i = 1; i < 10; i++) {
      for (int j = 1; j < 10; j++) {
        dbls.add(i * Math.pow(10, j));
        dbls.add(-i * Math.pow(10, j));
      }
    }

    Random rand = new Random(0);
    for (int i = 0; i < NUM_RANDOM_TESTS; i++) {
      double d = Double.longBitsToDouble(rand.nextLong());
      if (!Double.isNaN(d)) {
        dbls.add(d);
      }
    }

    return dbls;
  }

  @Test
  public void fpModelContent() throws SolverException, InterruptedException {
    FloatingPointFormula zeroVar = fpmgr.makeVariable("zero", singlePrecType);
    BooleanFormula zeroEq = fpmgr.assignment(zeroVar, zero);

    FloatingPointFormula oneVar = fpmgr.makeVariable("one", singlePrecType);
    BooleanFormula oneEq = fpmgr.assignment(oneVar, one);

    FloatingPointFormula nanVar = fpmgr.makeVariable("nan", singlePrecType);
    BooleanFormula nanEq = fpmgr.assignment(nanVar, nan);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(zeroEq);
      prover.push(oneEq);
      prover.push(nanEq);

      assertThat(prover).isSatisfiable();

      try (Model model = prover.getModel()) {

        FloatingPointNumber oneValue = model.evaluate(oneVar);
        ValueAssignment oneAssignment =
            new ValueAssignment(oneVar, one, oneEq, "one", oneValue, ImmutableList.of());

        FloatingPointNumber zeroValue = model.evaluate(zeroVar);
        ValueAssignment zeroAssignment =
            new ValueAssignment(zeroVar, zero, zeroEq, "zero", zeroValue, ImmutableList.of());

        FloatingPointNumber nanValue = model.evaluate(nanVar);
        ValueAssignment nanAssignment =
            new ValueAssignment(nanVar, nan, nanEq, "nan", nanValue, ImmutableList.of());

        assertThat(model).containsExactly(zeroAssignment, oneAssignment, nanAssignment);
      }
    }
  }

  @Test
  public void fpModelValue() throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.makeTrue());

      assertThat(prover).isSatisfiable();

      try (Model model = prover.getModel()) {
        assertThat(model).isEmpty();

        for (float f :
            new float[] {
              0,
              1,
              2,
              3,
              4,
              256,
              1000,
              1024,
              -1,
              -2,
              -3,
              -4,
              -1000,
              -1024,
              Float.NEGATIVE_INFINITY,
              Float.POSITIVE_INFINITY,
              Float.MAX_VALUE,
              Float.MIN_VALUE,
              Float.MIN_NORMAL,
            }) {
          var constFpNum = fpmgr.makeNumber(f, singlePrecType);
          FloatingPointNumber fpValue = model.evaluate(constFpNum);
          assertThat(fpValue.getMantissaSizeWithHiddenBit())
              .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit());
          assertThat(fpValue.getMantissaSizeWithoutHiddenBit())
              .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit() - 1);
          assertThat(fpValue.floatValue()).isEqualTo(f);
          assertThat(fpValue.doubleValue()).isEqualTo((double) f);
        }
      }
    }
  }

  // The standard defines the mantissa such that it includes the hidden bit, and mantissa +
  //  exponent equal the total size. This test checks this, + that it holds with to/from IEEE
  //  bitvector
  @Test
  public void bitvectorToFloatingPointMantissaSignBitInterpretationSinglePrecision() {
    int bvSize32 = singlePrecType.getTotalSize();
    BitvectorFormula bvNumber32 = bvmgr.makeBitvector(bvSize32, BigInteger.ZERO);
    // Sanity checks
    assertThat(bvSize32).isEqualTo(32);
    assertThat(singlePrecType.getExponentSize()).isEqualTo(8);
    assertThat(singlePrecType.getMantissaSizeWithoutHiddenBit()).isEqualTo(23);
    assertThat(singlePrecType.getMantissaSizeWithHiddenBit()).isEqualTo(24);
    assertThat(bvmgr.getLength(bvNumber32)).isEqualTo(bvSize32);
    assertThat(mgr.getFormulaType(bvNumber32).isBitvectorType()).isTrue();
    assertThat(((BitvectorType) mgr.getFormulaType(bvNumber32)).getSize()).isEqualTo(bvSize32);

    // Transform the BV to FP and check that it conforms to the precision used
    FloatingPointFormula bvToFpSinglePrec = fpmgr.fromIeeeBitvector(bvNumber32, singlePrecType);
    assertThat(mgr.getFormulaType(bvToFpSinglePrec).isFloatingPointType()).isTrue();
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpSinglePrec)).getTotalSize())
        .isEqualTo(singlePrecType.getTotalSize());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpSinglePrec))
                .getMantissaSizeWithHiddenBit())
        .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpSinglePrec))
                .getMantissaSizeWithoutHiddenBit())
        .isEqualTo(singlePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpSinglePrec)).getExponentSize())
        .isEqualTo(singlePrecType.getExponentSize());

    // The same as above, but build the precision by hand with the different APIs
    FloatingPointType fpTypeWithSignBit =
        getFloatingPointTypeFromSizesWithHiddenBit(
            singlePrecType.getExponentSize(), singlePrecType.getMantissaSizeWithHiddenBit());
    FloatingPointType fpTypeWithoutSignBit =
        getFloatingPointTypeFromSizesWithoutHiddenBit(
            singlePrecType.getExponentSize(), singlePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(fpTypeWithSignBit).isEqualTo(singlePrecType);
    assertThat(fpTypeWithoutSignBit).isEqualTo(singlePrecType);

    FloatingPointFormula bvToFpfpTypeWithSignBit =
        fpmgr.fromIeeeBitvector(bvNumber32, fpTypeWithSignBit);
    assertThat(mgr.getFormulaType(bvToFpfpTypeWithSignBit).isFloatingPointType()).isTrue();
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit)).getTotalSize())
        .isEqualTo(singlePrecType.getTotalSize());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit))
                .getMantissaSizeWithHiddenBit())
        .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit))
                .getMantissaSizeWithoutHiddenBit())
        .isEqualTo(singlePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit)).getExponentSize())
        .isEqualTo(singlePrecType.getExponentSize());

    FloatingPointFormula bvToFpfpTypeWithoutSignBit =
        fpmgr.fromIeeeBitvector(bvNumber32, fpTypeWithoutSignBit);
    assertThat(mgr.getFormulaType(bvToFpfpTypeWithoutSignBit).isFloatingPointType()).isTrue();
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit)).getTotalSize())
        .isEqualTo(singlePrecType.getTotalSize());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit))
                .getMantissaSizeWithHiddenBit())
        .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit))
                .getMantissaSizeWithoutHiddenBit())
        .isEqualTo(singlePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit)).getExponentSize())
        .isEqualTo(singlePrecType.getExponentSize());
  }

  @Test
  public void floatingPointMantissaSignBitWithBitvectorInterpretationSinglePrecision()
      throws SolverException, InterruptedException {
    requireNativeFPToBitvector();

    int bvSize32 = singlePrecType.getTotalSize();
    BitvectorFormula bvNumber32 = bvmgr.makeBitvector(bvSize32, BigInteger.ZERO);
    FloatingPointFormula bvToFpSinglePrec = fpmgr.fromIeeeBitvector(bvNumber32, singlePrecType);
    FloatingPointType fpTypeWithSignBit =
        getFloatingPointTypeFromSizesWithHiddenBit(
            singlePrecType.getExponentSize(), singlePrecType.getMantissaSizeWithHiddenBit());
    FloatingPointType fpTypeWithoutSignBit =
        getFloatingPointTypeFromSizesWithoutHiddenBit(
            singlePrecType.getExponentSize(), singlePrecType.getMantissaSizeWithoutHiddenBit());
    FloatingPointFormula bvToFpfpTypeWithSignBit =
        fpmgr.fromIeeeBitvector(bvNumber32, fpTypeWithSignBit);
    FloatingPointFormula bvToFpfpTypeWithoutSignBit =
        fpmgr.fromIeeeBitvector(bvNumber32, fpTypeWithoutSignBit);

    // Check FP to BV conversion in regard to precision (all above is asserted in
    //  bitvectorToFloatingPointMantissaSignBitInterpretationSinglePrecision())
    BitvectorFormula bvToFpSinglePrecToBv = fpmgr.toIeeeBitvector(bvToFpSinglePrec);
    assertThat(bvmgr.getLength(bvToFpSinglePrecToBv)).isEqualTo(bvSize32);

    BitvectorFormula bvToFpTypeWithSignBitToBv = fpmgr.toIeeeBitvector(bvToFpfpTypeWithSignBit);
    assertThat(bvmgr.getLength(bvToFpTypeWithSignBitToBv)).isEqualTo(bvSize32);

    BitvectorFormula bvToFpTypeWithoutSignBitToBv =
        fpmgr.toIeeeBitvector(bvToFpfpTypeWithoutSignBit);
    assertThat(bvmgr.getLength(bvToFpTypeWithoutSignBitToBv)).isEqualTo(bvSize32);

    assertThatFormula(bvmgr.equal(bvToFpSinglePrecToBv, bvNumber32)).isTautological();
    assertThatFormula(bvmgr.equal(bvToFpTypeWithSignBitToBv, bvNumber32)).isTautological();
    assertThatFormula(bvmgr.equal(bvToFpTypeWithoutSignBitToBv, bvNumber32)).isTautological();
  }

  // The standard defines the mantissa such that it includes the hidden bit, and mantissa +
  //  exponent equal the total size. This test checks this, + that it holds with from
  //  bitvector to IEEE FP
  @Test
  public void bitvectorToFloatingPointMantissaSignBitInterpretationDoublePrecision() {
    int bvSize64 = doublePrecType.getTotalSize();
    BitvectorFormula bvNumberSize64 = bvmgr.makeBitvector(bvSize64, BigInteger.ZERO);
    // Sanity checks
    assertThat(bvSize64).isEqualTo(64);
    assertThat(doublePrecType.getExponentSize()).isEqualTo(11);
    assertThat(doublePrecType.getMantissaSizeWithoutHiddenBit()).isEqualTo(52);
    assertThat(doublePrecType.getMantissaSizeWithHiddenBit()).isEqualTo(53);
    assertThat(bvmgr.getLength(bvNumberSize64)).isEqualTo(bvSize64);
    assertThat(mgr.getFormulaType(bvNumberSize64).isBitvectorType()).isTrue();
    assertThat(((BitvectorType) mgr.getFormulaType(bvNumberSize64)).getSize()).isEqualTo(bvSize64);

    // Transform the BV to FP and check that it conforms to the precision used
    FloatingPointFormula bvToFpDoublePrec = fpmgr.fromIeeeBitvector(bvNumberSize64, doublePrecType);
    assertThat(mgr.getFormulaType(bvToFpDoublePrec).isFloatingPointType()).isTrue();
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpDoublePrec)).getTotalSize())
        .isEqualTo(doublePrecType.getTotalSize());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpDoublePrec))
                .getMantissaSizeWithHiddenBit())
        .isEqualTo(doublePrecType.getMantissaSizeWithHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpDoublePrec))
                .getMantissaSizeWithoutHiddenBit())
        .isEqualTo(doublePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpDoublePrec)).getExponentSize())
        .isEqualTo(doublePrecType.getExponentSize());

    // The same as above, but build the precision by hand with the different APIs
    FloatingPointType fpTypeWithSignBit =
        getFloatingPointTypeFromSizesWithHiddenBit(
            doublePrecType.getExponentSize(), doublePrecType.getMantissaSizeWithHiddenBit());
    FloatingPointType fpTypeWithoutSignBit =
        getFloatingPointTypeFromSizesWithoutHiddenBit(
            doublePrecType.getExponentSize(), doublePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(fpTypeWithSignBit).isEqualTo(doublePrecType);
    assertThat(fpTypeWithoutSignBit).isEqualTo(doublePrecType);

    FloatingPointFormula bvToFpfpTypeWithSignBit =
        fpmgr.fromIeeeBitvector(bvNumberSize64, fpTypeWithSignBit);
    assertThat(mgr.getFormulaType(bvToFpfpTypeWithSignBit).isFloatingPointType()).isTrue();
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit)).getTotalSize())
        .isEqualTo(doublePrecType.getTotalSize());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit))
                .getMantissaSizeWithHiddenBit())
        .isEqualTo(doublePrecType.getMantissaSizeWithHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit))
                .getMantissaSizeWithoutHiddenBit())
        .isEqualTo(doublePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithSignBit)).getExponentSize())
        .isEqualTo(doublePrecType.getExponentSize());

    FloatingPointFormula bvToFpfpTypeWithoutSignBit =
        fpmgr.fromIeeeBitvector(bvNumberSize64, fpTypeWithoutSignBit);
    assertThat(mgr.getFormulaType(bvToFpfpTypeWithoutSignBit).isFloatingPointType()).isTrue();
    assertThat(((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit)).getTotalSize())
        .isEqualTo(doublePrecType.getTotalSize());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit))
                .getMantissaSizeWithHiddenBit())
        .isEqualTo(doublePrecType.getMantissaSizeWithHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit))
                .getMantissaSizeWithoutHiddenBit())
        .isEqualTo(doublePrecType.getMantissaSizeWithoutHiddenBit());
    assertThat(
            ((FloatingPointType) mgr.getFormulaType(bvToFpfpTypeWithoutSignBit)).getExponentSize())
        .isEqualTo(doublePrecType.getExponentSize());
  }

  // Checks the correct precision/exponent/mantissa in FP to BV conversion
  @Test
  public void floatingPointMantissaSignBitWithBitvectorInterpretationDoublePrecision()
      throws SolverException, InterruptedException {
    requireNativeFPToBitvector();

    int bvSize64 = doublePrecType.getTotalSize();
    BitvectorFormula bvNumberSize64 = bvmgr.makeBitvector(bvSize64, BigInteger.ZERO);
    FloatingPointFormula bvToFpDoublePrec = fpmgr.fromIeeeBitvector(bvNumberSize64, doublePrecType);
    FloatingPointType fpTypeWithSignBit =
        getFloatingPointTypeFromSizesWithHiddenBit(
            doublePrecType.getExponentSize(), doublePrecType.getMantissaSizeWithHiddenBit());
    FloatingPointType fpTypeWithoutSignBit =
        getFloatingPointTypeFromSizesWithoutHiddenBit(
            doublePrecType.getExponentSize(), doublePrecType.getMantissaSizeWithoutHiddenBit());
    FloatingPointFormula bvToFpfpTypeWithSignBit =
        fpmgr.fromIeeeBitvector(bvNumberSize64, fpTypeWithSignBit);
    FloatingPointFormula bvToFpfpTypeWithoutSignBit =
        fpmgr.fromIeeeBitvector(bvNumberSize64, fpTypeWithoutSignBit);

    // Check FP to BV conversion in regard to precision (all above is asserted in
    //  bitvectorToFloatingPointMantissaSignBitInterpretationDoublePrecision())
    BitvectorFormula bvToFpDoublePrecToBv = fpmgr.toIeeeBitvector(bvToFpDoublePrec);
    assertThat(bvmgr.getLength(bvToFpDoublePrecToBv)).isEqualTo(bvSize64);

    BitvectorFormula bvToFpTypeWithSignBitToBv = fpmgr.toIeeeBitvector(bvToFpfpTypeWithSignBit);
    assertThat(bvmgr.getLength(bvToFpTypeWithSignBitToBv)).isEqualTo(bvSize64);

    BitvectorFormula bvToFpTypeWithoutSignBitToBv =
        fpmgr.toIeeeBitvector(bvToFpfpTypeWithoutSignBit);
    assertThat(bvmgr.getLength(bvToFpTypeWithoutSignBitToBv)).isEqualTo(bvSize64);

    assertThatFormula(bvmgr.equal(bvToFpTypeWithSignBitToBv, bvNumberSize64)).isTautological();
    assertThatFormula(bvmgr.equal(bvToFpDoublePrecToBv, bvNumberSize64)).isTautological();
    assertThatFormula(bvmgr.equal(bvToFpTypeWithoutSignBitToBv, bvNumberSize64)).isTautological();
  }

  @Test
  @SuppressWarnings({"unchecked", "resource"})
  public void fpInterpolation() throws SolverException, InterruptedException {
    requireInterpolation();
    assume()
        .withMessage("MathSAT5 does not support floating-point interpolation")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    BooleanFormula f1 = fpmgr.equalWithFPSemantics(var, zero);
    BooleanFormula f2 = bmgr.not(fpmgr.isZero(var));
    try (InterpolatingProverEnvironment<Object> prover =
        (InterpolatingProverEnvironment<Object>) context.newProverEnvironmentWithInterpolation()) {
      Object itpGroup1 = prover.push(f1);
      prover.push(f2);

      assertThat(prover).isUnsatisfiable();

      BooleanFormula itp = prover.getInterpolant(ImmutableList.of(itpGroup1));
      assertThatFormula(f1).implies(itp);
      assertThatFormula(bmgr.and(itp, f2)).isUnsatisfiable();
    }
  }

  @Test
  public void failOnInvalidString() {
    assertThrows(Exception.class, () -> fpmgr.makeNumber("a", singlePrecType));
  }

  @Test
  public void failOnInvalidBvSizeInToIeeeFallback() {
    FloatingPointType fpType = singlePrecType;
    assertThrows(
        IllegalArgumentException.class,
        () ->
            fpmgr.toIeeeBitvector(
                fpmgr.makeVariable("someName1", fpType),
                bvmgr.makeVariable(fpType.getTotalSize() + 1, "someBv1")));
    assertThrows(
        IllegalArgumentException.class,
        () ->
            fpmgr.toIeeeBitvector(
                fpmgr.makeVariable("someName2", fpType),
                bvmgr.makeVariable(fpType.getTotalSize() - 1, "someBv2")));
    assertThrows(
        IllegalArgumentException.class,
        () ->
            fpmgr.toIeeeBitvector(
                fpmgr.makeVariable("someName3", fpType),
                bvmgr.makeVariable(
                    fpType.getExponentSize() + fpType.getMantissaSizeWithoutHiddenBit(),
                    "someBv3")));
  }

  @Test
  public void fpFrom32BitPattern() throws SolverException, InterruptedException {
    proveForAll(
        getListOfFloats(),
        pFloat -> {
          // makeFP(value.bits.sign, value.bits.exponent, value.bits.mantissa) = makeFP(value.float)
          int bits = Float.floatToRawIntBits(pFloat);
          int exponent = (bits >>> 23) & 0xFF;
          int mantissa = bits & 0x7FFFFF;
          Sign sign = Sign.of(bits < 0); // equal to: (bits >>> 31) & 0x1
          final FloatingPointFormula fpFromBv =
              fpmgr.makeNumber(
                  BigInteger.valueOf(exponent), BigInteger.valueOf(mantissa), sign, singlePrecType);
          final FloatingPointNumber fpNumber =
              FloatingPointNumber.of(
                  sign, BigInteger.valueOf(exponent), BigInteger.valueOf(mantissa), singlePrecType);
          assertThat(fpNumber.getMantissaSizeWithHiddenBit())
              .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit());
          assertThat(fpNumber.getMantissaSizeWithoutHiddenBit())
              .isEqualTo(singlePrecType.getMantissaSizeWithHiddenBit() - 1);
          final FloatingPointFormula fp1 = fpmgr.makeNumber(fpNumber);
          final FloatingPointFormula fp2 = fpmgr.makeNumber(pFloat, singlePrecType);
          final BooleanFormula assignment1 = fpmgr.assignment(fpFromBv, fp1);
          final BooleanFormula assignment2 = fpmgr.assignment(fpFromBv, fp2);
          return bmgr.and(assignment1, assignment2);
        });
  }

  @Test
  public void fpFrom64BitPattern() throws SolverException, InterruptedException {
    proveForAll(
        // makeFP(value.bits.sign, value.bits.exponent, value.bits.mantissa) = makeFP(value.float)
        getListOfDoubles(),
        pDouble -> {
          long bits = Double.doubleToRawLongBits(pDouble);
          long exponent = (bits >>> 52) & 0x7FF;
          long mantissa = bits & 0xFFFFFFFFFFFFFL;
          Sign sign = Sign.of(bits < 0); // equal to: (doubleBits >>> 63) & 1;
          final FloatingPointFormula fpFromBv =
              fpmgr.makeNumber(
                  BigInteger.valueOf(exponent), BigInteger.valueOf(mantissa), sign, doublePrecType);
          final FloatingPointNumber fpNumber =
              FloatingPointNumber.of(
                  sign, BigInteger.valueOf(exponent), BigInteger.valueOf(mantissa), doublePrecType);
          assertThat(fpNumber.getMantissaSizeWithHiddenBit())
              .isEqualTo(doublePrecType.getMantissaSizeWithHiddenBit());
          assertThat(fpNumber.getMantissaSizeWithoutHiddenBit())
              .isEqualTo(doublePrecType.getMantissaSizeWithHiddenBit() - 1);
          final FloatingPointFormula fp1 = fpmgr.makeNumber(fpNumber);
          final FloatingPointFormula fp2 = fpmgr.makeNumber(pDouble, doublePrecType);
          final BooleanFormula assignment1 = fpmgr.assignment(fpFromBv, fp1);
          final BooleanFormula assignment2 = fpmgr.assignment(fpFromBv, fp2);
          return bmgr.and(assignment1, assignment2);
        });
  }

  @Test
  public void fpFromNumberIntoTooNarrowType() throws SolverException, InterruptedException {
    // near zero rounds to zero, if precision is too narrow
    for (double nearZero : new double[] {Double.MIN_VALUE, Float.MIN_VALUE / 2d}) {
      assertThatFormula(
              fpmgr.equalWithFPSemantics(zero, fpmgr.makeNumber(nearZero, singlePrecType)))
          .isTautological();
      assertThatFormula(
              fpmgr.equalWithFPSemantics(negZero, fpmgr.makeNumber(-nearZero, singlePrecType)))
          .isTautological();
    }

    // near infinity rounds to infinity, if precision is too narrow
    for (double nearInf : new double[] {Double.MAX_VALUE, Float.MAX_VALUE * 2d}) {
      assertThatFormula(
              fpmgr.equalWithFPSemantics(posInf, fpmgr.makeNumber(nearInf, singlePrecType)))
          .isTautological();
      assertThatFormula(
              fpmgr.equalWithFPSemantics(negInf, fpmgr.makeNumber(-nearInf, singlePrecType)))
          .isTautological();
    }
  }
}
