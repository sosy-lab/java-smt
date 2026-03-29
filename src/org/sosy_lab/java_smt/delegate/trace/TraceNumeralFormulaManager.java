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
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class TraceNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {
  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;
  private final TraceLogger logger;

  TraceNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  private String getPrefix() {
    return getFormulaType().equals(FormulaType.IntegerType)
        ? "mgr.getIntegerFormulaManager()"
        : "mgr.getRationalFormulaManager()";
  }

  @Override
  public ResultFormulaType makeNumber(long number) {
    return logger.logDef(
        getPrefix(), "makeNumber(%s)".formatted(number), () -> delegate.makeNumber(number));
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger number) {
    return logger.logDef(
        getPrefix(),
        "makeNumber(new BigInteger(\"%s\"))".formatted(number),
        () -> delegate.makeNumber(number));
  }

  @Override
  public ResultFormulaType makeNumber(double number) {
    return logger.logDef(
        getPrefix(), "makeNumber(%s)".formatted(number), () -> delegate.makeNumber(number));
  }

  @Override
  public ResultFormulaType makeNumber(BigDecimal number) {
    return logger.logDef(
        getPrefix(),
        "makeNumber(new BigDecimal(\"%s\"))".formatted(number),
        () -> delegate.makeNumber(number));
  }

  @Override
  public ResultFormulaType makeNumber(String pI) {
    return logger.logDef(
        getPrefix(), "makeNumber(\"%s\")".formatted(pI), () -> delegate.makeNumber(pI));
  }

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    return logger.logDef(
        getPrefix(),
        "makeNumber(Rational.of(\"%s\"))".formatted(pRational),
        () -> delegate.makeNumber(pRational));
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    return logger.logDef(
        getPrefix(),
        "makeVariable(%s)".formatted(logger.printString(pVar)),
        () -> delegate.makeVariable(pVar));
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType number) {
    return logger.logDef(
        getPrefix(),
        "negate(%s)".formatted(logger.toVariable(number)),
        () -> delegate.negate(number));
  }

  @Override
  public ResultFormulaType add(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "add(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.add(number1, number2));
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    return logger.logDef(
        getPrefix(),
        "sum(%s)".formatted(logger.toVariables(operands)),
        () -> delegate.sum(operands));
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "subtract(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.subtract(number1, number2));
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType numerator, ParamFormulaType denominator) {
    return logger.logDef(
        getPrefix(),
        "divide(%s, %s)".formatted(logger.toVariable(numerator), logger.toVariable(denominator)),
        () -> delegate.divide(numerator, denominator));
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "multiply(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.multiply(number1, number2));
  }

  @Override
  public BooleanFormula equal(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "equal(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.equal(number1, number2));
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    return logger.logDef(
        getPrefix(),
        "distinct(%s)".formatted(logger.toVariables(pNumbers)),
        () -> delegate.distinct(pNumbers));
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "greaterThan(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterThan(number1, number2));
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "greaterOrEquals(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "lessThan(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessThan(number1, number2));
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        getPrefix(),
        "lessOrEquals(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessOrEquals(number1, number2));
  }

  @Override
  public IntegerFormula floor(ParamFormulaType formula) {
    return logger.logDef(
        getPrefix(),
        "floor(%s)".formatted(logger.toVariable(formula)),
        () -> delegate.floor(formula));
  }
}
