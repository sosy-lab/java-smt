/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

class TraceFloatingPointFormulaManager implements FloatingPointFormulaManager {
  private final FloatingPointFormulaManager delegate;
  private final TraceLogger logger;

  TraceFloatingPointFormulaManager(FloatingPointFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  private String printRoundingMode(FloatingPointRoundingMode pRoundingMode) {
    return "FloatingPointRoundingMode." + pRoundingMode.name();
  }

  private String printSign(Sign pSign) {
    return "FloatingPointNumber.Sign." + pSign.name();
  }

  private String printDouble(double number) {
    if (Double.isNaN(number)) {
      return "Double.NaN";
    } else if (Double.isInfinite(number)) {
      return number > 0 ? "Double.POSITIVE_INFINITY" : "Double.NEGATIVE_INFINITY";
    } else if (number == 0.0
        && Double.doubleToRawLongBits(number) == Double.doubleToRawLongBits(-0.0)) {
      return "-0.0";
    } else {
      return Double.toString(number);
    }
  }

  @Override
  public FloatingPointRoundingModeFormula makeRoundingMode(
      FloatingPointRoundingMode pRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeRoundingMode(%s)".formatted("FloatingPointRoundingMode." + pRoundingMode.name()),
        () -> delegate.makeRoundingMode(pRoundingMode));
  }

  @Override
  public FloatingPointRoundingMode fromRoundingModeFormula(
      FloatingPointRoundingModeFormula pRoundingModeFormula) {
    return logger.logDefDiscard(
        "mgr.getFloatingPointFormulaManager()",
        "fromRoundingModeFormula(%s)".formatted(logger.toVariable(pRoundingModeFormula)),
        () -> delegate.fromRoundingModeFormula(pRoundingModeFormula));
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FloatingPointType type) {
    return makeNumber(n, type, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeNumber(%s, %s, %s)"
            .formatted(
                printDouble(n),
                logger.printFormulaType(type),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type) {
    return makeNumber(n, type, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeNumber(new BigDecimal(\"%s\"), %s, %s)"
            .formatted(
                n, logger.printFormulaType(type), printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FloatingPointType type) {
    return makeNumber(n, type, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeNumber(\"%s\", %s, %s)"
            .formatted(
                n, logger.printFormulaType(type), printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FloatingPointType type) {
    return makeNumber(n, type, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeNumber(Rational.of(\"%s\"), %s, %s)"
            .formatted(
                n, logger.printFormulaType(type), printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeNumber(new BigInteger(\"%s\"), new BigInteger(\"%s\"), %s, %s)"
            .formatted(exponent, mantissa, printSign(sign), logger.printFormulaType(type)),
        () -> delegate.makeNumber(exponent, mantissa, sign, type));
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeVariable(%s, %s)".formatted(logger.printString(pVar), logger.printFormulaType(type)),
        () -> delegate.makeVariable(pVar, type));
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makePlusInfinity(%s)".formatted(logger.printFormulaType(type)),
        () -> delegate.makePlusInfinity(type));
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeMinusInfinity(%s)".formatted(logger.printFormulaType(type)),
        () -> delegate.makeMinusInfinity(type));
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "makeNaN(%s)".formatted(logger.printFormulaType(type)),
        () -> delegate.makeNaN(type));
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType) {
    return castTo(source, signed, targetType, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "castTo(%s, %s, %s, %s)"
            .formatted(
                logger.toVariable(source),
                signed,
                logger.printFormulaType(targetType),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.castTo(source, signed, targetType, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source, boolean signed, FloatingPointType targetType) {
    return castFrom(source, signed, targetType, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "castFrom(%s, %s, %s, %s)"
            .formatted(
                logger.toVariable(source),
                signed,
                logger.printFormulaType(targetType),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.castFrom(source, signed, targetType, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula number, FloatingPointType pTargetType) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "fromIeeeBitvector(%s, %s)"
            .formatted(logger.toVariable(number), logger.printFormulaType(pTargetType)),
        () -> delegate.fromIeeeBitvector(number, pTargetType));
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "toIeeeBitvector(%s)".formatted(logger.toVariable(number)),
        () -> delegate.toIeeeBitvector(number));
  }

  @Override
  public BooleanFormula bitwiseEqual(
      FloatingPointFormula floatValue, BitvectorFormula bitvectorValue) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "toIeeeBitvector(%s, %s)"
            .formatted(logger.toVariable(floatValue), logger.toVariable(bitvectorValue)),
        () -> delegate.bitwiseEqual(floatValue, bitvectorValue));
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula formula, FloatingPointRoundingMode roundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "round(%s, %s)".formatted(logger.toVariable(formula), printRoundingMode(roundingMode)),
        () -> delegate.round(formula, roundingMode));
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "negate(%s)".formatted(logger.toVariable(number)),
        () -> delegate.negate(number));
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "abs(%s)".formatted(logger.toVariable(number)),
        () -> delegate.abs(number));
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "max(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.max(number1, number2));
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "min(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.min(number1, number2));
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    return sqrt(number, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "sqrt(%s, %s)".formatted(logger.toVariable(number), printRoundingMode(roundingMode)),
        () -> delegate.sqrt(number, roundingMode));
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2) {
    return add(number1, number2, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "add(%s, %s, %s)"
            .formatted(
                logger.toVariable(number1),
                logger.toVariable(number2),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.add(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2) {
    return subtract(number1, number2, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "subtract(%s, %s, %s)"
            .formatted(
                logger.toVariable(number1),
                logger.toVariable(number2),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.subtract(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2) {
    return divide(number1, number2, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "divide(%s, %s, %s)"
            .formatted(
                logger.toVariable(number1),
                logger.toVariable(number2),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.divide(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2) {
    return multiply(number1, number2, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "multiply(%s, %s, %s)"
            .formatted(
                logger.toVariable(number1),
                logger.toVariable(number2),
                printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.multiply(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula dividend, FloatingPointFormula divisor) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "remainder(%s, %s)".formatted(logger.toVariable(dividend), logger.toVariable(divisor)),
        () -> delegate.remainder(dividend, divisor));
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "assignment(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.assignment(number1, number2));
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "equalWithFPSemantics(%s, %s)"
            .formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.equalWithFPSemantics(number1, number2));
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "greaterThan(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterThan(number1, number2));
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "greaterOrEquals(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "lessThan(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessThan(number1, number2));
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "lessOrEquals(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "isNaN(%s)".formatted(logger.toVariable(number)),
        () -> delegate.isNaN(number));
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "isInfinity(%s)".formatted(logger.toVariable(number)),
        () -> delegate.isInfinity(number));
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "isZero(%s)".formatted(logger.toVariable(number)),
        () -> delegate.isZero(number));
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "isNormal(%s)".formatted(logger.toVariable(number)),
        () -> delegate.isNormal(number));
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "isSubnormal(%s)".formatted(logger.toVariable(number)),
        () -> delegate.isSubnormal(number));
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        "isNegative(%s)".formatted(logger.toVariable(number)),
        () -> delegate.isNegative(number));
  }
}
