// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import java.math.BigInteger;
import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.Generator;

@SuppressWarnings({"all"})
public class FloatingPointSMTLIB2GeneratorTest
    extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  @Test
  public void testMakeVariable() {
    requireFloats();
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeFloatingPoint() {
    requireFloats();
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula c =
        fpmgr.makeVariable("c", FormulaType.getSinglePrecisionFloatingPointType());
    BooleanFormula assign1 =
        fpmgr.equalWithFPSemantics(
            a,
            fpmgr.makeNumber(
                10.0,
                FloatingPointType.getSinglePrecisionFloatingPointType(),
                FloatingPointRoundingMode.TOWARD_ZERO));
    BooleanFormula assign2 =
        fpmgr.equalWithFPSemantics(
            b, fpmgr.makeNumber(15.0, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula assign3 =
        fpmgr.equalWithFPSemantics(
            c, fpmgr.makeNumber(25.0, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.add(a, b), c);
    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a (fp #b0 #b10000010 #b01000000000000000000000)))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq b (fp #b0 #b10000010 #b11100000000000000000000)))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp #b0 #b10000011 #b10010000000000000000000)))\n"
            + "(assert (fp.eq (fp.add a b) c))\n";
    Generator.assembleConstraint(assign1);
    Generator.assembleConstraint(assign2);
    Generator.assembleConstraint(assign3);
    Generator.assembleConstraint(constraint);
    String actualResult = String.valueOf(Generator.getLines());
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPAdd() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.add(a, b), result);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.add a b) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPSub() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.subtract(a, b), result);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.sub a b) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPDiv() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.divide(a, b), result);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.div a b) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPMul() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.multiply(a, b), result);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.mul a b) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPSqrt() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.sqrt(a), result);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.sqrt a) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPIsNaN() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula isNaN = fpmgr.isNaN(a);

    Generator.assembleConstraint(isNaN);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n" + "(assert (fp.isNaN a))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPIsZero() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula isZero = fpmgr.isZero(a);

    Generator.assembleConstraint(isZero);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n" + "(assert (fp.isZero a))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPMax() {
    requireFloats();
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula max =
        fpmgr.makeVariable("max", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.max(a, b), max);
    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const max (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.max a b) max))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPMin() {
    requireFloats();
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula min =
        fpmgr.makeVariable("min", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(fpmgr.min(a, b), min);
    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const min (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq (fp.min a b) min))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakePlusInfinity() {
    requireFloats();
    FloatingPointFormula plusInfinity =
        fpmgr.makeVariable("plusInfinity", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(
            plusInfinity,
            fpmgr.makePlusInfinity(FloatingPointType.getSinglePrecisionFloatingPointType()));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const plusInfinity (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq plusInfinity (_ +oo 8 24)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeMinusInfinity() {
    requireFloats();
    FloatingPointFormula minusInfinity =
        fpmgr.makeVariable(
            "minusInfinity", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(
            minusInfinity,
            fpmgr.makeMinusInfinity(FloatingPointType.getSinglePrecisionFloatingPointType()));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const minusInfinity (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq minusInfinity (_ -oo 8 24)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeNaN() {
    requireFloats();
    FloatingPointFormula nan =
        fpmgr.makeVariable("nan", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(
            nan, fpmgr.makeNaN(FloatingPointType.getSinglePrecisionFloatingPointType()));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const nan (_ FloatingPoint 8 24))\n" + "(assert (fp.eq nan (_ NaN 8 24)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCastTo() {
    requireFloats();
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    BitvectorFormula castResult = bvmgr.makeVariable(32, "castResult");
    BooleanFormula constraint =
        bvmgr.equal(fpmgr.castTo(a, true, FormulaType.getBitvectorTypeWithSize(32)), castResult);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const castResult (_ BitVec 32))\n"
            + "(assert (= ((_ fp.to_sbv 32) a) castResult))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCastFrom() {
    assume()
        .withMessage("Bitwuzla and Mathsat5 do not support boolean casting")
        .that(!solverToUse().equals(Solvers.BITWUZLA) && !solverToUse().equals(Solvers.MATHSAT5))
        .isTrue();
    requireFloats();
    BooleanFormula b = bmgr.makeVariable("b");
    FloatingPointFormula castResult =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());

    Generator.assembleConstraint(
        fpmgr.equalWithFPSemantics(
            castResult,
            fpmgr.castFrom(b, true, FloatingPointType.getSinglePrecisionFloatingPointType())));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(declare-const b Bool)\n"
            + "(assert (fp.eq result ((_ to_fp 8 24) b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFromIeeeBitvector() {
    requireFloats();
    requireBitvectors();
    String bvs = "00000000000000000000000000000000";
    BitvectorFormula bv = bvmgr.makeBitvector(32, new BigInteger(bvs, 2));
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());

    Generator.assembleConstraint(
        fpmgr.equalWithFPSemantics(
            fpmgr.fromIeeeBitvector(bv, FloatingPointType.getSinglePrecisionFloatingPointType()),
            result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq ((_ to_fp 8 24) #b00000000000000000000000000000000) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFromIeeeBitvectorWithVariable() {
    requireFloats();
    requireBitvectors();
    BitvectorFormula bv = bvmgr.makeVariable(32, "bv");
    FloatingPointFormula result =
        fpmgr.makeVariable("result", FloatingPointType.getSinglePrecisionFloatingPointType());

    Generator.assembleConstraint(
        fpmgr.equalWithFPSemantics(
            fpmgr.fromIeeeBitvector(bv, FloatingPointType.getSinglePrecisionFloatingPointType()),
            result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const bv (_ BitVec 32))\n"
            + "(declare-const result (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq ((_ to_fp 8 24) bv) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRound() {
    requireFloats();
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());

    Generator.assembleConstraint(
        fpmgr.equalWithFPSemantics(
            a, fpmgr.round(a, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN)));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a (_ FloatingPoint 8 24))\n" + "(assert (fp.eq a (fp.round RNE a)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
}
