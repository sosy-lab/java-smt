/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

@SuppressWarnings("UnusedVariable")
public class PortfolioFloatingPointFormulaManager implements FloatingPointFormulaManager {

  private final PortfolioFormulaCreator creator;
  private final FloatingPointRoundingMode floatingPointRoundingMode;

  public PortfolioFloatingPointFormulaManager(
      PortfolioFormulaCreator pCreator, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    creator = pCreator;
    floatingPointRoundingMode = pFloatingPointRoundingMode;
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType type) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source, boolean signed, FloatingPointType targetType) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula number, FloatingPointType pTargetType) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula formula, FloatingPointRoundingMode roundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula dividend, FloatingPointFormula divisor) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    throw new UnsupportedOperationException("implement me");
  }
}
