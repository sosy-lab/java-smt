// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

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

public class DebuggingFloatingPointFormulaManager implements FloatingPointFormulaManager {
  private final FloatingPointFormulaManager delegate;
  private final DebuggingAssertions debugging;

  DebuggingFloatingPointFormulaManager(
      FloatingPointFormulaManager pDelegate, DebuggingAssertions pDebugging) {
    delegate = pDelegate;
    debugging = pDebugging;
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(exponent, mantissa, sign, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeVariable(pVar, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makePlusInfinity(type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeMinusInfinity(type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType type) {
    debugging.assertThreadLocal();
    FloatingPointFormula result = delegate.makeNaN(type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(source);
    T result = delegate.castTo(source, signed, targetType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(source);
    T result = delegate.castTo(source, signed, targetType, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source, boolean signed, FloatingPointType targetType) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(source);
    FloatingPointFormula result = delegate.castFrom(source, signed, targetType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(source);
    FloatingPointFormula result =
        delegate.castFrom(source, signed, targetType, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula number, FloatingPointType pTargetType) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    FloatingPointFormula result = delegate.fromIeeeBitvector(number, pTargetType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BitvectorFormula result = delegate.toIeeeBitvector(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula formula, FloatingPointRoundingMode roundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    FloatingPointFormula result = delegate.round(formula, roundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    FloatingPointFormula result = delegate.negate(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    FloatingPointFormula result = delegate.abs(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.max(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.min(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    FloatingPointFormula result = delegate.sqrt(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    FloatingPointFormula result = delegate.sqrt(number, roundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.add(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.add(number1, number2, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.subtract(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.subtract(number1, number2, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.divide(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.divide(number1, number2, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.multiply(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.multiply(number1, number2, pFloatingPointRoundingMode);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula dividend, FloatingPointFormula divisor) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(dividend);
    debugging.assertFormulaInContext(divisor);
    FloatingPointFormula result = delegate.remainder(dividend, divisor);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.assignment(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.equalWithFPSemantics(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterThan(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterOrEquals(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessThan(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessOrEquals(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BooleanFormula result = delegate.isNaN(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BooleanFormula result = delegate.isInfinity(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BooleanFormula result = delegate.isZero(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BooleanFormula result = delegate.isNormal(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BooleanFormula result = delegate.isSubnormal(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BooleanFormula result = delegate.isNegative(number);
    debugging.addFormulaTerm(result);
    return result;
  }
}
