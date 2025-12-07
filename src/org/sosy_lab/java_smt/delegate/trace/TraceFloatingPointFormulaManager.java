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

public class TraceFloatingPointFormulaManager implements FloatingPointFormulaManager {
  private final FloatingPointFormulaManager delegate;
  private final TraceLogger logger;

  TraceFloatingPointFormulaManager(FloatingPointFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  private String printRoundingMode(FloatingPointRoundingMode pRoundingMode) {
    return "FloatingPointRoundingMode." + pRoundingMode.name();
  }

  private String toString(double number) {
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
        String.format("makeRoundingMode(%s)", "FloatingPointRoundingMode." + pRoundingMode.name()),
        () -> delegate.makeRoundingMode(pRoundingMode));
  }

  @Override
  public FloatingPointRoundingMode fromRoundingModeFormula(
      FloatingPointRoundingModeFormula pRoundingModeFormula) {
    return delegate.fromRoundingModeFormula(pRoundingModeFormula);
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeNumber(%s, %s)", toString(n), logger.printFormulaType(type)),
        () -> delegate.makeNumber(n, type));
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "makeNumber(%s, %s, %s)",
            toString(n),
            logger.printFormulaType(type),
            printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeNumber(new BigDecimal(\"%s\"), %s)", n, logger.printFormulaType(type)),
        () -> delegate.makeNumber(n, type));
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "makeNumber(new BigDecimal(\"%s\"), %s, %s)",
            n, logger.printFormulaType(type), printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeNumber(\"%s\", %s)", n, logger.printFormulaType(type)),
        () -> delegate.makeNumber(n, type));
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "makeNumber(\"%s\", %s, %s)",
            n, logger.printFormulaType(type), printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeNumber(Rational.of(\"%s\"), %s)", n, logger.printFormulaType(type)),
        () -> delegate.makeNumber(n, type));
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "makeNumber(Rational.of(%s, %s), %s, %s)",
            n.getNum(),
            n.getDen(),
            logger.printFormulaType(type),
            printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.makeNumber(n, type, pFloatingPointRoundingMode));
  }

  private String printSign(Sign pSign) {
    return "FloatingPointNumber.Sign." + pSign.name();
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "makeNumber(new BigInteger(\"%s\"), new BigInteger(\"%s\"), %s, %s)",
            exponent, mantissa, printSign(sign), logger.printFormulaType(type)),
        () -> delegate.makeNumber(exponent, mantissa, sign, type));
  }

  @Override
  public FloatingPointFormula makeVariable(String pVar, FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeVariable(\"%s\", %s)", pVar, logger.printFormulaType(type)),
        () -> delegate.makeVariable(pVar, type));
  }

  @Override
  public FloatingPointFormula makePlusInfinity(FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makePlusInfinity(%s)", logger.printFormulaType(type)),
        () -> delegate.makePlusInfinity(type));
  }

  @Override
  public FloatingPointFormula makeMinusInfinity(FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeMinusInfinity(%s)", logger.printFormulaType(type)),
        () -> delegate.makeMinusInfinity(type));
  }

  @Override
  public FloatingPointFormula makeNaN(FloatingPointType type) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("makeNaN(%s)", logger.printFormulaType(type)),
        () -> delegate.makeNaN(type));
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "castTo(%s, %s, %s)",
            logger.toVariable(source), signed, logger.printFormulaType(targetType)),
        () -> delegate.castTo(source, signed, targetType));
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "castTo(%s, %s, %s, %s)",
            logger.toVariable(source),
            signed,
            logger.printFormulaType(targetType),
            printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.castTo(source, signed, targetType, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source, boolean signed, FloatingPointType targetType) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "castFrom(%s, %s, %s)",
            logger.toVariable(source), signed, logger.printFormulaType(targetType)),
        () -> delegate.castFrom(source, signed, targetType));
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "castFrom(%s, %s, %s, %s)",
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
        String.format(
            "fromIeeeBitvector(%s, %s)",
            logger.toVariable(number), logger.printFormulaType(pTargetType)),
        () -> delegate.fromIeeeBitvector(number, pTargetType));
  }

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("toIeeeBitvector(%s)", logger.toVariable(number)),
        () -> delegate.toIeeeBitvector(number));
  }

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula formula, FloatingPointRoundingMode roundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("round(%s, %s)", logger.toVariable(formula), printRoundingMode(roundingMode)),
        () -> delegate.round(formula, roundingMode));
  }

  @Override
  public FloatingPointFormula negate(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("negate(%s)", logger.toVariable(number)),
        () -> delegate.negate(number));
  }

  @Override
  public FloatingPointFormula abs(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("abs(%s)", logger.toVariable(number)),
        () -> delegate.abs(number));
  }

  @Override
  public FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("max(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.max(number1, number2));
  }

  @Override
  public FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("min(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.min(number1, number2));
  }

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("sqrt(%s)", logger.toVariable(number)),
        () -> delegate.sqrt(number));
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode roundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("sqrt(%s, %s)", logger.toVariable(number), printRoundingMode(roundingMode)),
        () -> delegate.sqrt(number, roundingMode));
  }

  @Override
  public FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("add(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.add(number1, number2));
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "add(%s, %s, %s)",
            logger.toVariable(number1),
            logger.toVariable(number2),
            printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.add(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("subtract(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.subtract(number1, number2));
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "subtract(%s, %s, %s)",
            logger.toVariable(number1),
            logger.toVariable(number2),
            printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.subtract(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("divide(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.divide(number1, number2));
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "divide(%s, %s, %s)",
            logger.toVariable(number1),
            logger.toVariable(number2),
            printRoundingMode(pFloatingPointRoundingMode)),
        () -> delegate.divide(number1, number2, pFloatingPointRoundingMode));
  }

  @Override
  public FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("multiply(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.multiply(number1, number2));
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "multiply(%s, %s, %s)",
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
        String.format("remainder(%s, %s)", logger.toVariable(dividend), logger.toVariable(divisor)),
        () -> delegate.remainder(dividend, divisor));
  }

  @Override
  public BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("assignment(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.assignment(number1, number2));
  }

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "equalWithFPSemantics(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.equalWithFPSemantics(number1, number2));
  }

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "greaterThan(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterThan(number1, number2));
  }

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "greaterOrEquals(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("lessThan(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessThan(number1, number2));
  }

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format(
            "lessOrEquals(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula isNaN(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("isNaN(%s)", logger.toVariable(number)),
        () -> delegate.isNaN(number));
  }

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("isInfinity(%s)", logger.toVariable(number)),
        () -> delegate.isInfinity(number));
  }

  @Override
  public BooleanFormula isZero(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("isZero(%s)", logger.toVariable(number)),
        () -> delegate.isZero(number));
  }

  @Override
  public BooleanFormula isNormal(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("isNormal(%s)", logger.toVariable(number)),
        () -> delegate.isNormal(number));
  }

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("isSubnormal(%s)", logger.toVariable(number)),
        () -> delegate.isSubnormal(number));
  }

  @Override
  public BooleanFormula isNegative(FloatingPointFormula number) {
    return logger.logDef(
        "mgr.getFloatingPointFormulaManager()",
        String.format("isNegative(%s)", logger.toVariable(number)),
        () -> delegate.isNegative(number));
  }
}
