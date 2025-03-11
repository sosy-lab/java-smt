// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Objects;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

@SuppressWarnings({"CheckReturnValue", "ReturnValueIgnored"})
public class SMTLIB2FloatingPointTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Before
  public void setup() {
    Generator.setIsLoggingEnabled(true);
  }

  @After
  public void teardown() {
    Generator.setIsLoggingEnabled(false);
    Generator.resetGenerator();
  }

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  @Before
  public void setUp() {
    assume().that(fpmgr).isNotNull();
  }

  @Test
  public void testCastFloatingPointWithDoubles()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume()
        .withMessage("Bitwuzla doesn't support rational theory")
        .that(!solverToUse().equals(Solvers.BITWUZLA))
        .isTrue();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq c ((_ to_fp 8 24) RNE 20.0)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    FloatingPointFormula a =
        Objects.requireNonNull(fpmgr)
            .makeVariable("a", FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        Objects.requireNonNull(fpmgr)
            .makeVariable("b", FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula c =
        Objects.requireNonNull(fpmgr)
            .makeVariable("c", FormulaType.getSinglePrecisionFloatingPointType());
    BooleanFormula constraint1 =
        fpmgr.equalWithFPSemantics(
            a,
            fpmgr.castFrom(
                rmgr.makeNumber(10.0), true, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint2 =
        fpmgr.equalWithFPSemantics(
            b,
            fpmgr.castFrom(
                rmgr.makeNumber(10.0), true, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint3 =
        fpmgr.equalWithFPSemantics(
            c,
            fpmgr.castFrom(
                rmgr.makeNumber(20.0), true, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint4 = fpmgr.equalWithFPSemantics(fpmgr.add(a, b), c);
    BooleanFormula expectedResult = bmgr.and(constraint1, constraint2, constraint3, constraint4);
    assertThat(actualResult).isNotNull();
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  private final FormulaType.FloatingPointType fpType =
      FormulaType.getSinglePrecisionFloatingPointType();

  @Test
  public void testMakeFloatingPointFromDouble()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    String smtInput =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a (fp #b0 #x82 #b01000000000000000000000)))\n"
            + "(assert (fp.eq b (fp #b0 #x82 #b01000000000000000000000)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(smtInput);

    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a", fpType);
    FloatingPointFormula b = Objects.requireNonNull(fpmgr).makeVariable("b", fpType);
    FloatingPointFormula c = Objects.requireNonNull(fpmgr).makeVariable("c", fpType);

    BooleanFormula expectedResult =
        bmgr.and(
            fpmgr.equalWithFPSemantics(a, fpmgr.makeNumber(10.0, fpType)),
            fpmgr.equalWithFPSemantics(b, fpmgr.makeNumber(10.0, fpType)),
            fpmgr.equalWithFPSemantics(fpmgr.add(a, b), c));
    assertThat(actualResult).isNotNull();
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeFloatingPointFromReal()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume().withMessage("Whole Real theory is not supported in JavaSMT yet").that(false).isTrue();
    String smtInput =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE 3/2)))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE 3/2)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(smtInput);

    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a", fpType);
    FloatingPointFormula b = Objects.requireNonNull(fpmgr).makeVariable("b", fpType);
    FloatingPointFormula c = Objects.requireNonNull(fpmgr).makeVariable("c", fpType);

    BooleanFormula expectedResult =
        bmgr.and(
            fpmgr.equalWithFPSemantics(
                a,
                fpmgr.makeNumber(
                    Rational.of(new BigInteger("3", 10), new BigInteger("2", 10)), fpType)),
            fpmgr.equalWithFPSemantics(
                b,
                fpmgr.makeNumber(
                    Rational.of(new BigInteger("3", 10), new BigInteger("2", 10)), fpType)),
            fpmgr.equalWithFPSemantics(c, fpmgr.add(a, b)));
    Generator.assembleConstraint(actualResult);
    assertThat(actualResult).isNotNull();
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeFloatingPointFromBigDecimal()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume()
        .withMessage("Bitwuzla doesn't support rational theory")
        .that(!solverToUse().equals(Solvers.BITWUZLA))
        .isTrue();
    String smtInput =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE 3.14159)))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE 3.14159)))\n"
            + "(assert (fp.eq c ((_ to_fp 8 24) RNE 6.28318)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(smtInput);

    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a", fpType);
    FloatingPointFormula b = Objects.requireNonNull(fpmgr).makeVariable("b", fpType);
    FloatingPointFormula c = Objects.requireNonNull(fpmgr).makeVariable("c", fpType);

    BooleanFormula constraint =
        bmgr.and(
            fpmgr.equalWithFPSemantics(a, fpmgr.makeNumber(new BigDecimal("3.14159"), fpType)),
            fpmgr.equalWithFPSemantics(b, fpmgr.makeNumber(new BigDecimal("3.14159"), fpType)),
            fpmgr.equalWithFPSemantics(c, fpmgr.makeNumber(new BigDecimal("6.28318"), fpType)),
            fpmgr.equalWithFPSemantics(c, fpmgr.add(a, b)));
    Generator.assembleConstraint(actualResult);
    assertThat(actualResult).isNotNull();
    assertThat(constraint.equals(actualResult));
  }

  @Test
  public void testMakeFloatingPointFromString()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
    assume()
        .withMessage("Bitwuzla doesn't support String theory")
        .that(!solverToUse().equals(Solvers.BITWUZLA))
        .isTrue();
    String smtInput =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE \"2.71828\")))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE \"2.71828\")))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(smtInput);

    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a", fpType);
    FloatingPointFormula b = Objects.requireNonNull(fpmgr).makeVariable("b", fpType);
    FloatingPointFormula c = Objects.requireNonNull(fpmgr).makeVariable("c", fpType);
    BooleanFormula expectedResult =
        bmgr.and(
            fpmgr.equalWithFPSemantics(a, fpmgr.makeNumber("2.71828", fpType)),
            fpmgr.equalWithFPSemantics(b, fpmgr.makeNumber("2.71828", fpType)),
            fpmgr.equalWithFPSemantics(c, fpmgr.add(a, b)));
    Generator.assembleConstraint(actualResult);
    assertThat(actualResult).isNotNull();
    assertThat(actualResult.equals(expectedResult));
  }

  @Test
  public void testDeclareFloatingPoints()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a b))\n";

    checkAndCreate(x);
  }

  private void checkAndCreate(String pX)
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    BooleanFormula actualResult = mgr.universalParseFromString(pX);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    Generator.assembleConstraint(actualResult);
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointAddition()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a  (_ FloatingPoint 8 24))\n"
            + "(declare-const b  (_ FloatingPoint 8 24))\n"
            + "(declare-const c  (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp.add RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula additionResult =
        fpmgr.add(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, additionResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareFloatingPointsWithBits()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireFloats();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a (fp #b0 #b10000010 #b01000000000000000000000)))\n"
            + "(assert (fp.eq b (fp #b0 #b10000010 #b01000000000000000000000)))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    FloatingPointFormula c =
        fpmgr.makeNumber(10.0, FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula d =
        fpmgr.makeNumber(10.0, FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getSinglePrecisionFloatingPointType());
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getSinglePrecisionFloatingPointType());
    BooleanFormula expectedResult =
        bmgr.and(fpmgr.equalWithFPSemantics(a, c), fpmgr.equalWithFPSemantics(b, d));
    Generator.assembleConstraint(actualResult);
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareFloatingPointsWithBitVectors()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireFloats();
    requireBitvectors();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a ((_ to_fp 8 24) #b00000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getSinglePrecisionFloatingPointType());
    BitvectorFormula bitvector =
        bvmgr.makeBitvector(32, new BigInteger("00000000000000000000000000000000", 2));
    FloatingPointFormula b =
        fpmgr.fromIeeeBitvector(bitvector, FormulaType.getSinglePrecisionFloatingPointType());
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = fpmgr.equalWithFPSemantics(a, b);
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareFloat8()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 5 3))\n"
            + "(declare-const b  (_ FloatingPoint 5 3))\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(5, 2));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(5, 2));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareFloat16()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float16)\n" + "(declare-const b Float16)\n" + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(5, 10));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(5, 10));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareFloat32()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float32)\n" + "(declare-const b Float32)\n" + "(assert (fp.eq a b))\n";

    checkAndCreate(x);
  }

  @Test
  public void testDeclareFloat64()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float64)\n" + "(declare-const b Float64)\n" + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(11, 52));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(11, 52));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareFloat128()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float128)\n" + "(declare-const b Float128)\n" + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(15, 112));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(15, 112));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointMultiplication()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp.mul RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula multiplicationResult =
        fpmgr.multiply(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, multiplicationResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointSubtraction()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp.sub RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula subtractionResult =
        fpmgr.subtract(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, subtractionResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointDivision()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp.div RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula divisionResult =
        fpmgr.divide(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, divisionResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointNegation()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq b (fp.neg a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula negationResult = fpmgr.negate(a);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(b, negationResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointAbsoluteValue()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq b (fp.abs a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula absResult = fpmgr.abs(a);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(b, absResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointMax()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp.max a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula maxResult = fpmgr.max(a, b);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, maxResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointMin()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq c (fp.min a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula minResult = fpmgr.min(a, b);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, minResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointSquareRoot()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq b (fp.sqrt RNE a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 23));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 23));

    FloatingPointFormula sqrtResult = fpmgr.sqrt(a, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(b, sqrtResult);
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointInfinity()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const inf (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq inf (_ +oo 8 "
            + "24)))"
            + "\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula inf =
        fpmgr.makeVariable("inf", FormulaType.getSinglePrecisionFloatingPointType());

    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(
            inf, fpmgr.makePlusInfinity(FormulaType.getSinglePrecisionFloatingPointType()));
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointNaN()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const nan (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq nan (_ NaN 8 "
            + "24)))"
            + "\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula nan = fpmgr.makeVariable("nan", FormulaType.getFloatingPointType(8, 23));

    BooleanFormula constraint =
        fpmgr.equalWithFPSemantics(
            nan, fpmgr.makeNaN(FormulaType.getSinglePrecisionFloatingPointType()));
    Generator.assembleConstraint(actualResult);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(actualResult).isEqualTo(expectedResult);
  }
}
