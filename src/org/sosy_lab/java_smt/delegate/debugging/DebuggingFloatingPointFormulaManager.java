// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.math.BigDecimal;
import java.util.Set;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

public class DebuggingFloatingPointFormulaManager extends FormulaChecks
    implements FloatingPointFormulaManager {
  private final FloatingPointFormulaManager delegate;

  public DebuggingFloatingPointFormulaManager(
      FloatingPointFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = pDelegate;
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNumber(n, type, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeVariable(pVar, type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makePlusInfinity(type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeMinusInfinity(type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType type) {
    assertThreadLocal();
    FloatingPointFormula result = delegate.makeNaN(type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType) {
    assertThreadLocal();
    assertFormulaInContext(source);
    T result = delegate.castTo(source, signed, targetType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    assertFormulaInContext(source);
    T result = delegate.castTo(source, signed, targetType, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source, boolean signed, FloatingPointType targetType) {
    assertThreadLocal();
    assertFormulaInContext(source);
    FloatingPointFormula result = delegate.castFrom(source, signed, targetType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    assertFormulaInContext(source);
    FloatingPointFormula result =
        delegate.castFrom(source, signed, targetType, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula number, FloatingPointType pTargetType) {
    assertThreadLocal();
    assertFormulaInContext(number);
    FloatingPointFormula result = delegate.fromIeeeBitvector(number, pTargetType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BitvectorFormula result = delegate.toIeeeBitvector(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula formula, FloatingPointRoundingMode roundingMode) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    FloatingPointFormula result = delegate.round(formula, roundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    FloatingPointFormula result = delegate.negate(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    FloatingPointFormula result = delegate.abs(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.max(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.min(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    FloatingPointFormula result = delegate.sqrt(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    assertThreadLocal();
    assertFormulaInContext(number);
    FloatingPointFormula result = delegate.sqrt(number, roundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.add(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.add(number1, number2, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.subtract(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.subtract(number1, number2, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.divide(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.divide(number1, number2, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.multiply(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    FloatingPointFormula result = delegate.multiply(number1, number2, pFloatingPointRoundingMode);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.assignment(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.equalWithFPSemantics(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterThan(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterOrEquals(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessThan(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessOrEquals(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BooleanFormula result = delegate.isNaN(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BooleanFormula result = delegate.isInfinity(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BooleanFormula result = delegate.isZero(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BooleanFormula result = delegate.isNormal(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BooleanFormula result = delegate.isSubnormal(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BooleanFormula result = delegate.isNormal(number);
    addFormulaToContext(result);
    return result;
  }
}
