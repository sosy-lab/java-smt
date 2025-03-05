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
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

@SuppressWarnings({"CheckReturnValue", "ReturnValueIgnored"})
public class SMTLIB2FloatingPointTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

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
  public void testMakeFloatingPoint()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
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
            a, fpmgr.makeNumber(10.0, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint2 =
        fpmgr.equalWithFPSemantics(
            a, fpmgr.makeNumber(10.0, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint3 =
        fpmgr.equalWithFPSemantics(
            c, fpmgr.makeNumber(20.0, FormulaType.getSinglePrecisionFloatingPointType()));
    BooleanFormula constraint4 = fpmgr.equalWithFPSemantics(fpmgr.add(a, b), c);
    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint2);
    Generator.assembleConstraint(constraint3);
    Generator.assembleConstraint(constraint4);
    System.out.println(Generator.getLines());
    BooleanFormula expectedResult = bmgr.and(constraint1, constraint2, constraint3, constraint4);
    assertThat(actualResult).isNotNull();
    assertThat(expectedResult.equals(actualResult));
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
            + "(assert (fp.eq a ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq b ((_ to_fp 8 24) RNE 10.0)))\n"
            + "(assert (fp.eq (fp.add RNE a b) c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(smtInput);

    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a", fpType);
    FloatingPointFormula b = Objects.requireNonNull(fpmgr).makeVariable("b", fpType);
    FloatingPointFormula c = Objects.requireNonNull(fpmgr).makeVariable("c", fpType);

    BooleanFormula expectedResult =
        bmgr.and(
            fpmgr.equalWithFPSemantics(a, fpmgr.makeNumber(10.0, fpType)),
            fpmgr.equalWithFPSemantics(b, fpmgr.makeNumber(10.0, fpType)),
            fpmgr.equalWithFPSemantics(c, fpmgr.add(a, b)));
    assertThat(actualResult).isNotNull();
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testMakeFloatingPointFromRational()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
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
    assertThat(actualResult).isNotNull();
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testMakeFloatingPointFromBigDecimal()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
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
    assertThat(actualResult).isNotNull();
    assertThat(constraint.equals(actualResult));
  }

  @Test
  public void testMakeFloatingPointFromString()
      throws SolverException, InterruptedException, IOException, InvalidConfigurationException {
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

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointAddition()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a  (_ FloatingPoint 8 24))\n"
            + "(declare-const b  (_ FloatingPoint 8 24))\n"
            + "(declare-const c  (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.add RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula additionResult =
        fpmgr.add(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, additionResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testDeclareFloatingPointsWithBitVectors()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireFloats();
    requireBitvectors();
    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (= b ((_ to_fp 8 24) RNE #b00000000000000000000000000000000)))\n"
            + "(fp.eq a b)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);
    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getSinglePrecisionFloatingPointType());
    BitvectorFormula bitvector = bvmgr.makeBitvector(32, 12345);
    FloatingPointFormula b =
        fpmgr.fromIeeeBitvector(bitvector, FormulaType.getSinglePrecisionFloatingPointType());

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testDeclareFloat8()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 5 3))\n"
            + "(declare-const b  (_ FloatingPoint 5 3))\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(5, 3));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(5, 3));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testDeclareFloat16()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float16)\n" + "(declare-const b Float16)\n" + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(5, 11));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(5, 11));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
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

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(11, 53));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(11, 53));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testDeclareFloat128()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float128)\n" + "(declare-const b Float128))\n" + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(15, 113));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(15, 113));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointMultiplication()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.mul RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula multiplicationResult =
        fpmgr.multiply(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, multiplicationResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointSubtraction()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.sub RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula subtractionResult =
        fpmgr.subtract(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, subtractionResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointDivision()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.div RNE a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula divisionResult =
        fpmgr.divide(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, divisionResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointNegation()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (= b (fp.neg a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula negationResult = fpmgr.negate(a);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(b, negationResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointAbsoluteValue()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (= b (fp.abs a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula absResult = fpmgr.abs(a);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(b, absResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointMax()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.max a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula maxResult = fpmgr.max(a, b);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, maxResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointMin()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(declare-const c (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.min a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c = fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula minResult = fpmgr.min(a, b);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, minResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointSquareRoot()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (= b (fp.sqrt RNE a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b = fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula sqrtResult = fpmgr.sqrt(a, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(b, sqrtResult);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointInfinity()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x = "(declare-const inf (_ FloatingPoint 8 24))\n" + "(assert (= inf (_ +oo 8 24)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula inf = fpmgr.makePlusInfinity(FormulaType.getFloatingPointType(8, 24));

    BooleanFormula constraint = fpmgr.isInfinity(inf);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointNaN()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x = "(declare-const nan (_ FloatingPoint 8 24))\n" + "(assert (= nan (_ NaN 8 24)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula nan = fpmgr.makeNaN(FormulaType.getFloatingPointType(8, 24));

    BooleanFormula constraint = fpmgr.isNaN(nan);

    BooleanFormula expectedResult = constraint;
    Generator.assembleConstraint(expectedResult);
    assertThat(expectedResult.equals(actualResult));
  }

  /*
   Make Test for this :
  (
  (define-fun a () (_ FloatingPoint 8 24) (fp #b1 #b01111110 #b01010101010101010101011))
  (define-fun b () (_ FloatingPoint 8 24) (fp #b1 #b01111110 #b11111111111111111111111))
  (define-fun c () (_ FloatingPoint 8 24) (fp #b1 #b01111110 #b11111111111111111111111))
  (define-fun rm () RoundingMode roundTowardPositive)
  )
  (((fp.fma rm a b c) (fp #b1 #b01111101 #b01010101010101010101001)))
  (((fp.add rm (fp.mul rm a b) c) (fp #b1 #b01111101 #b01010101010101010101000)))
     */
}
