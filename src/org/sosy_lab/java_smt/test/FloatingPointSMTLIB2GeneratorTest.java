package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class FloatingPointSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  @Test
  public void testMakeVariable() {
    requireFloats();
    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a",
        FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = Objects.requireNonNull(fpmgr).makeVariable("b",
        FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(assert (fp.eq a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPAdd() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result = fpmgr.add(a,b);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(result, (fpmgr.add(a,b)));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.add RNE a b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
  @Test
  public void testFPSub() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result = fpmgr.subtract(a, b);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(result, fpmgr.subtract(a, b));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.sub RNE a b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPDiv() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result = fpmgr.divide(a, b);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(result, fpmgr.divide(a, b));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.div RNE a b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPMul() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result = fpmgr.multiply(a, b);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(result, fpmgr.multiply(a, b));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.mul RNE a b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPSqrt() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula result = fpmgr.sqrt(a);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(result, fpmgr.sqrt(a));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.sqrt RNE a)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPIsNaN() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula isNaN = fpmgr.isNaN(a);

    Generator.assembleConstraint(isNaN);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(assert (fp.isNaN a))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPIsZero() {
    requireFloats();
    Objects.requireNonNull(fpmgr);
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula isZero = fpmgr.isZero(a);

    Generator.assembleConstraint(isZero);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(assert (fp.isZero a))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPMax() {
    requireFloats();
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula max = fpmgr.max(a, b);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(max, fpmgr.max(a, b));
    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.max a b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFPMin() {
    requireFloats();
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b = fpmgr.makeVariable("b", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula min = fpmgr.min(a, b);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(min, fpmgr.min(a, b));
    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const b (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (= result (fp.min a b)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakePlusInfinity() {
    requireFloats();
    FloatingPointFormula plusInfinity = fpmgr.makeVariable("plusInfinity",
        FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(plusInfinity,
            fpmgr.makePlusInfinity(FloatingPointType.getSinglePrecisionFloatingPointType()));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const plusInfinity (_ FloatingPoint 8 23))\n"
        + "(assert (fp.eq plusInfinity (_ +oo 8 23)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeMinusInfinity() {
    requireFloats();
    FloatingPointFormula minusInfinity = fpmgr.makeVariable("minusInfinity",
        FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(minusInfinity,
            fpmgr.makeMinusInfinity(FloatingPointType.getSinglePrecisionFloatingPointType()));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const minusInfinity (_ FloatingPoint 8 23))\n"
        + "(assert (fp.eq minusInfinity (_ -oo 8 23)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeNaN() {
    requireFloats();
    FloatingPointFormula nan = fpmgr.makeNaN(FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(nan,
        fpmgr.makeNaN(FloatingPointType.getSinglePrecisionFloatingPointType()));


    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const nan (_ FloatingPoint 8 23))\n"
        + "(assert (fp.eq nan (_ NaN 8 23)\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCastTo() {
    requireFloats();
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    BooleanFormula castResult = fpmgr.castTo(a, true, FormulaType.BooleanType);

    Generator.assembleConstraint(castResult);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(assert ((_ cast_to BooleanType true) a))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCastFrom() {
    requireFloats();
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula castResult = fpmgr.castFrom(b, true, FloatingPointType.getSinglePrecisionFloatingPointType());

    Generator.assembleConstraint(fpmgr.equalWithFPSemantics(b, castResult));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const b Bool)\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert ((_ cast_from Bool true) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFromIeeeBitvector() {
    requireFloats();
    BitvectorFormula bitvector = bvmgr.makeVariable(BitvectorType.getBitvectorTypeWithSize(32),
        "bv");
    FloatingPointFormula fpFromBV = fpmgr.makeVariable("fpFromBV", FloatingPointType.getSinglePrecisionFloatingPointType());


    Generator.assembleConstraint(fpmgr.equalWithFPSemantics(fpFromBV, fpmgr.fromIeeeBitvector(bitvector, FloatingPointType.getSinglePrecisionFloatingPointType())));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const bv (_ BitVec 32))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert ((_ to_fp 8 23) bv))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
  @Test
  public void testRound() {
    requireFloats();
    FloatingPointFormula a = fpmgr.makeVariable("a", FloatingPointType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula rounded = fpmgr.round(a, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    Generator.assembleConstraint(fpmgr.equalWithFPSemantics(a, rounded));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a (_ FloatingPoint 8 23))\n"
        + "(declare-const result (_ FloatingPoint 8 23))\n"
        + "(assert (fp.round RNE a))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }



}
