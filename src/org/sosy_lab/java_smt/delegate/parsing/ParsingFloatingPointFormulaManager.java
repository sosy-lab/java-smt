/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

public class ParsingFloatingPointFormulaManager implements FloatingPointFormulaManager {
  private final FloatingPointFormulaManager delegate;
  private final ParsingFormulaManager.Declarations declarations;

  public ParsingFloatingPointFormulaManager(
      FloatingPointFormulaManager pDelegate, ParsingFormulaManager.Declarations pDeclarations) {
    delegate = pDelegate;
    declarations = pDeclarations;
  }

  @Override
  public FloatingPointRoundingModeFormula makeRoundingMode(
      FloatingPointRoundingMode pRoundingMode) {
    return delegate.makeRoundingMode(pRoundingMode);
  }

  @Override
  public FloatingPointRoundingMode fromRoundingModeFormula(
      FloatingPointRoundingModeFormula pRoundingModeFormula) {
    return delegate.fromRoundingModeFormula(pRoundingModeFormula);
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FormulaType.FloatingPointType type) {
    return delegate.makeNumber(n, type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n,
      FormulaType.FloatingPointType type,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.makeNumber(n, type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FormulaType.FloatingPointType type) {
    return delegate.makeNumber(n, type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n,
      FormulaType.FloatingPointType type,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.makeNumber(n, type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FormulaType.FloatingPointType type) {
    return delegate.makeNumber(n, type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n,
      FormulaType.FloatingPointType type,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.makeNumber(n, type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FormulaType.FloatingPointType type) {
    return delegate.makeNumber(n, type);
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n,
      FormulaType.FloatingPointType type,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.makeNumber(n, type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent,
      BigInteger mantissa,
      FloatingPointNumber.Sign sign,
      FormulaType.FloatingPointType type) {
    return delegate.makeNumber(exponent, mantissa, sign, type);
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FormulaType.FloatingPointType type) {
    FloatingPointFormula term = delegate.makeVariable(pVar, type);
    declarations.addConstant(pVar, term);
    return term;
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FormulaType.FloatingPointType type) {
    return delegate.makePlusInfinity(type);
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FormulaType.FloatingPointType type) {
    return delegate.makeMinusInfinity(type);
  }

  @Override
  public FloatingPointFormula makeNaN(FormulaType.FloatingPointType type) {
    return delegate.makeNaN(type);
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType) {
    return delegate.castTo(source, signed, targetType);
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.castTo(source, signed, targetType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source, boolean signed, FormulaType.FloatingPointType targetType) {
    return delegate.castFrom(source, signed, targetType);
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FormulaType.FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.castFrom(source, signed, targetType, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula number, FormulaType.FloatingPointType pTargetType) {
    return delegate.fromIeeeBitvector(number, pTargetType);
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    return delegate.toIeeeBitvector(number);
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula formula, FloatingPointRoundingMode roundingMode) {
    return delegate.round(formula, roundingMode);
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula number) {
    return delegate.negate(number);
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    return delegate.abs(number);
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.max(number1, number2);
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.min(number1, number2);
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    return delegate.sqrt(number);
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    return delegate.sqrt(number, roundingMode);
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.add(number1, number2);
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.add(number1, number2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.subtract(number1, number2);
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.subtract(number1, number2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.divide(number1, number2);
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.divide(number1, number2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.multiply(number1, number2);
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return delegate.multiply(number1, number2, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula dividend, FloatingPointFormula divisor) {
    return delegate.remainder(dividend, divisor);
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.assignment(number1, number2);
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.equalWithFPSemantics(number1, number2);
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.greaterThan(number1, number2);
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.greaterOrEquals(number1, number2);
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.lessThan(number1, number2);
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2) {
    return delegate.lessOrEquals(number1, number2);
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    return delegate.isNaN(number);
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    return delegate.isInfinity(number);
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    return delegate.isZero(number);
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    return delegate.isNormal(number);
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    return delegate.isSubnormal(number);
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    return delegate.isNegative(number);
  }
}
