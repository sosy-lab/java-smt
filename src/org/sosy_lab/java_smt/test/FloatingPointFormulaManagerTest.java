/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.rationals.ExtendedRational;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

@RunWith(Parameterized.class)
public class FloatingPointFormulaManagerTest extends SolverBasedTest0 {

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

  private FloatingPointType singlePrecType;
  private FloatingPointFormula nan;
  private FloatingPointFormula posInf;
  private FloatingPointFormula negInf;
  private FloatingPointFormula zero;

  @Before
  public void init() {
    requireFloats();

    singlePrecType = FormulaType.getSinglePrecisionFloatingPointType();
    nan = fpmgr.makeNaN(singlePrecType);
    posInf = fpmgr.makePlusInfinity(singlePrecType);
    negInf = fpmgr.makeMinusInfinity(singlePrecType);
    zero = fpmgr.makeNumber(0.0, singlePrecType);
  }

  @Test
  public void floatingPointType() {
    FloatingPointType type = FormulaType.getFloatingPointType(23, 42);
    FloatingPointFormula var = fpmgr.makeVariable("x", type);
    FloatingPointType result = (FloatingPointType) mgr.getFormulaType(var);

    assertThat(result.getExponentSize()).named("exponent size").isEqualTo(type.getExponentSize());
    assertThat(result.getMantissaSize()).named("mantissa size").isEqualTo(type.getMantissaSize());
  }

  @Test
  public void nanEqualNanIsUnsat() throws Exception {
    assertThatFormula(fpmgr.equalWithFPSemantics(nan, nan)).isUnsatisfiable();
  }

  @Test
  public void nanAssignedNanIsTrue() throws Exception {
    assertThatFormula(fpmgr.assignment(nan, nan)).isTautological();
  }

  @Test
  public void infinityOrdering() throws Exception {
    BooleanFormula order1 = fpmgr.greaterThan(posInf, zero);
    BooleanFormula order2 = fpmgr.greaterThan(zero, negInf);
    BooleanFormula order3 = fpmgr.greaterThan(posInf, negInf);

    assertThatFormula(bmgr.and(order1, order2, order3)).isTautological();
  }

  @Test
  public void infinityVariableOrdering() throws Exception {
    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    BooleanFormula varIsNan = fpmgr.isNaN(var);

    BooleanFormula order1 = fpmgr.greaterOrEquals(posInf, var);
    BooleanFormula order2 = fpmgr.lessOrEquals(negInf, var);

    assertThatFormula(bmgr.or(varIsNan, bmgr.and(order1, order2))).isTautological();
  }

  @Test
  public void specialValueFunctions() throws Exception {
    assertThatFormula(fpmgr.isInfinity(posInf)).isTautological();
    assertThatFormula(fpmgr.isInfinity(negInf)).isTautological();

    assertThatFormula(fpmgr.isNaN(nan)).isTautological();

    assertThatFormula(fpmgr.isZero(zero)).isTautological();
    assertThatFormula(fpmgr.isZero(fpmgr.makeNumber(-0.0, singlePrecType))).isTautological();

    FloatingPointFormula minPosNormalValue = fpmgr.makeNumber(Float.MIN_NORMAL, singlePrecType);
    assertThatFormula(fpmgr.isSubnormal(minPosNormalValue)).isUnsatisfiable();
    assertThatFormula(fpmgr.isZero(minPosNormalValue)).isUnsatisfiable();
  }

  @Test
  public void specialDoubles() throws Exception {
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
      throws Exception {
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
  public void numberConstants() throws Exception {
    FloatingPointType doublePrecType = FormulaType.getDoublePrecisionFloatingPointType();
    checkEqualityOfNumberConstantsFor(1.0, singlePrecType);
    checkEqualityOfNumberConstantsFor(-5.8774717541114375E-39, singlePrecType);
    checkEqualityOfNumberConstantsFor(-5.8774717541114375E-39, doublePrecType);
    checkEqualityOfNumberConstantsFor(3.4028234663852886e+38, singlePrecType);
    checkEqualityOfNumberConstantsFor(3.4028234663852886e+38, doublePrecType);
  }

  @Test
  public void cast() throws Exception {
    FloatingPointType doublePrecType = FormulaType.getDoublePrecisionFloatingPointType();
    FloatingPointFormula doublePrecNumber = fpmgr.makeNumber(1.5, doublePrecType);
    FloatingPointFormula singlePrecNumber = fpmgr.makeNumber(1.5, singlePrecType);

    FloatingPointFormula narrowedNumber = fpmgr.castTo(doublePrecNumber, singlePrecType);
    FloatingPointFormula widenedNumber = fpmgr.castTo(singlePrecNumber, doublePrecType);

    assertThatFormula(fpmgr.equalWithFPSemantics(narrowedNumber, singlePrecNumber))
        .isTautological();
    assertThatFormula(fpmgr.equalWithFPSemantics(widenedNumber, doublePrecNumber)).isTautological();

    FloatingPointFormula doublePrecSmallNumber =
        fpmgr.makeNumber(5.8774717541114375E-39, doublePrecType);
    FloatingPointFormula singlePrecSmallNumber =
        fpmgr.makeNumber(5.8774717541114375E-39, singlePrecType);
    FloatingPointFormula widenedSmallNumber = fpmgr.castTo(singlePrecSmallNumber, doublePrecType);
    assertThatFormula(fpmgr.equalWithFPSemantics(widenedSmallNumber, doublePrecSmallNumber))
        .isTautological();
  }

  @Test
  public void bvToFpOne() throws Exception {
    requireBitvectors();

    BitvectorFormula bvOne = bvmgr.makeBitvector(32, 1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    FloatingPointFormula signedBvToFpOne = fpmgr.castFrom(bvOne, true, singlePrecType);
    FloatingPointFormula unsignedBvToFpOne = fpmgr.castFrom(bvOne, false, singlePrecType);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, signedBvToFpOne)).isTautological();
    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, unsignedBvToFpOne)).isTautological();
  }

  /** check whether rounded input is equal to result with rounding-mode. */
  private void round0(
      double value, double toZero, double pos, double neg, double tiesEven, double tiesAway)
      throws Exception {
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
    assertEquals(
        fpmgr.makeNumber(toZero, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_ZERO));

    assertEquals(
        fpmgr.makeNumber(pos, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_POSITIVE));

    assertEquals(
        fpmgr.makeNumber(neg, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_NEGATIVE));

    assertEquals(
        fpmgr.makeNumber(tiesEven, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN));

    if (solver != Solvers.MATHSAT5) { // Mathsat does not support NEAREST_TIES_AWAY
      assertEquals(
          fpmgr.makeNumber(tiesAway, singlePrecType),
          fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_AWAY));
    }
  }

  private void assertEquals(FloatingPointFormula f1, FloatingPointFormula f2) throws Exception {
    assertThatFormula(fpmgr.equalWithFPSemantics(f1, f2)).isTautological();
  }

  @Test
  public void round() throws Exception {

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
  public void bvToFpMinusOne() throws Exception {
    requireBitvectors();

    BitvectorFormula bvOne = bvmgr.makeBitvector(32, -1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    // A 32bit value "-1" when interpreted as unsigned is 2^31 - 1
    FloatingPointFormula fpMinInt = fpmgr.makeNumber(Math.pow(2, 32) - 1, singlePrecType);

    FloatingPointFormula unsignedBvToFpOne = fpmgr.castFrom(bvOne, false, singlePrecType);
    FloatingPointFormula signedBvToFpOne = fpmgr.castFrom(bvOne, true, singlePrecType);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, signedBvToFpOne)).isTautological();
    assertThatFormula(fpmgr.equalWithFPSemantics(fpMinInt, unsignedBvToFpOne)).isTautological();
  }

  @Test
  public void fpToBvOne() throws Exception {
    requireBitvectors();

    BitvectorFormula bvOne = bvmgr.makeBitvector(32, 1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    BitvectorFormula fpToBvOne = fpmgr.castTo(fpOne, FormulaType.getBitvectorTypeWithSize(32));

    assertThatFormula(bvmgr.equal(bvOne, fpToBvOne)).isTautological();
  }

  @Test
  public void fpToBvMinusOne() throws Exception {
    requireBitvectors();

    BitvectorFormula bvOne = bvmgr.makeBitvector(32, -1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    BitvectorFormula fpToBvOne = fpmgr.castTo(fpOne, FormulaType.getBitvectorTypeWithSize(32));
    assertThatFormula(bvmgr.equal(bvOne, fpToBvOne)).isTautological();
  }

  @Test
  public void rationalToFpOne() throws Exception {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    FloatingPointFormula ratToFpOne = fpmgr.castFrom(ratOne, true, singlePrecType);
    FloatingPointFormula unsignedRatToFpOne = fpmgr.castFrom(ratOne, false, singlePrecType);
    assertThat(unsignedRatToFpOne).isEqualTo(ratToFpOne);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, ratToFpOne)).isSatisfiable();
  }

  @Test
  public void rationalToFpMinusOne() throws Exception {
    requireBitvectors();

    NumeralFormula ratOne = rmgr.makeNumber(-1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    FloatingPointFormula ratToFpOne = fpmgr.castFrom(ratOne, true, singlePrecType);
    FloatingPointFormula unsignedRatToFpOne = fpmgr.castFrom(ratOne, false, singlePrecType);
    assertThat(unsignedRatToFpOne).isEqualTo(ratToFpOne);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, ratToFpOne)).isSatisfiable();
  }

  @Test
  public void fpToRationalOne() throws Exception {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    NumeralFormula fpToRatOne = fpmgr.castTo(fpOne, FormulaType.RationalType);

    assertThatFormula(rmgr.equal(ratOne, fpToRatOne)).isSatisfiable();
  }

  @Test
  public void fpToRationalMinusOne() throws Exception {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(-1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    NumeralFormula fpToRatOne = fpmgr.castTo(fpOne, FormulaType.RationalType);

    assertThatFormula(rmgr.equal(ratOne, fpToRatOne)).isSatisfiable();
  }

  @Test
  public void fpTraversal() throws Exception {
    assertThat(mgr.extractVariables(zero)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(zero)).isEmpty();

    FloatingPointFormula one = fpmgr.makeNumber(1.0, singlePrecType);
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
  public void fpTraversalWithRoundingMode() throws Exception {
    FloatingPointFormula two = fpmgr.makeNumber(2.0, singlePrecType);
    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    FloatingPointFormula mult = fpmgr.multiply(two, var);
    assertThat(mgr.extractVariables(mult)).containsExactly("x", var);
    assertThat(mgr.extractVariablesAndUFs(mult)).containsExactly("x", var);
  }

  @Test
  public void fpIeeeConversionTypes() throws Exception {
    assume()
        .withMessage("FP-BV conversion of Z3 misses sign bit")
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    FloatingPointFormula var = fpmgr.makeVariable("var", singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.toIeeeBitvector(var)))
        .isEqualTo(FormulaType.getBitvectorTypeWithSize(32));
  }

  @Test
  public void fpIeeeConversion() throws Exception {
    assume()
        .withMessage("FP-BV conversion of Z3 misses sign bit")
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    FloatingPointFormula var = fpmgr.makeVariable("var", singlePrecType);
    assertThatFormula(
            fpmgr.assignment(
                var, fpmgr.fromIeeeBitvector(fpmgr.toIeeeBitvector(var), singlePrecType)))
        .isTautological();
  }

  @Test
  public void ieeeFpConversion() throws Exception {
    assume()
        .withMessage("FP-BV conversion of Z3 misses sign bit")
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    BitvectorFormula var = bvmgr.makeBitvector(32, 123456789);
    assertThatFormula(
            bvmgr.equal(var, fpmgr.toIeeeBitvector(fpmgr.fromIeeeBitvector(var, singlePrecType))))
        .isTautological();
  }

  @Test
  public void fpModelValue() throws Exception {
    FloatingPointFormula zeroVar = fpmgr.makeVariable("zero", singlePrecType);
    BooleanFormula zeroEq = fpmgr.assignment(zeroVar, zero);

    FloatingPointFormula oneVar = fpmgr.makeVariable("one", singlePrecType);
    BooleanFormula oneEq = fpmgr.assignment(oneVar, fpmgr.makeNumber(1.0, singlePrecType));

    FloatingPointFormula nanVar = fpmgr.makeVariable("nan", singlePrecType);
    BooleanFormula nanEq = fpmgr.assignment(nanVar, nan);

    FloatingPointFormula posInfVar = fpmgr.makeVariable("posInf", singlePrecType);
    BooleanFormula posInfEq = fpmgr.assignment(posInfVar, posInf);

    FloatingPointFormula negInfVar = fpmgr.makeVariable("negInf", singlePrecType);
    BooleanFormula negInfEq = fpmgr.assignment(negInfVar, negInf);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(zeroEq);
      prover.push(oneEq);
      prover.push(nanEq);
      prover.push(posInfEq);
      prover.push(negInfEq);

      assertThat(prover).isSatisfiable();

      try (Model model = prover.getModel()) {

        Object zeroValue = model.evaluate(zeroVar);
        ValueAssignment zeroAssignment =
            new ValueAssignment(zeroVar, "zero", zeroValue, ImmutableList.of());
        assertThat(zeroValue)
            .isAnyOf(ExtendedRational.ZERO, Rational.ZERO, BigDecimal.ZERO, 0.0, 0.0f);

        Object oneValue = model.evaluate(oneVar);
        ValueAssignment oneAssignment =
            new ValueAssignment(oneVar, "one", oneValue, ImmutableList.of());
        assertThat(oneValue)
            .isAnyOf(new ExtendedRational(Rational.ONE), Rational.ONE, BigDecimal.ONE, 1.0, 1.0f);

        Object nanValue = model.evaluate(nanVar);
        ValueAssignment nanAssignment =
            new ValueAssignment(nanVar, "nan", nanValue, ImmutableList.of());
        assertThat(nanValue).isAnyOf(ExtendedRational.NaN, Double.NaN, Float.NaN);

        Object posInfValue = model.evaluate(posInfVar);
        ValueAssignment posInfAssignment =
            new ValueAssignment(posInfVar, "posInf", posInfValue, ImmutableList.of());
        assertThat(posInfValue)
            .isAnyOf(ExtendedRational.INFTY, Double.POSITIVE_INFINITY, Float.POSITIVE_INFINITY);

        Object negInfValue = model.evaluate(negInfVar);
        ValueAssignment negInfAssignment =
            new ValueAssignment(negInfVar, "negInf", negInfValue, ImmutableList.of());
        assertThat(negInfValue)
            .isAnyOf(ExtendedRational.NEG_INFTY, Double.NEGATIVE_INFINITY, Float.NEGATIVE_INFINITY);

        assertThat(model)
            .containsExactly(
                zeroAssignment, oneAssignment, nanAssignment, posInfAssignment, negInfAssignment);
      }
    }
  }

  @Test
  @SuppressWarnings("unchecked")
  public void fpInterpolation() throws Exception {
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
}
