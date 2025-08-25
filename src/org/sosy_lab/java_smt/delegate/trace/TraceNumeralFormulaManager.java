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

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;

@SuppressWarnings("InterfaceTypeParameterName")
public abstract class TraceNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {
  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;
  private final TraceLogger logger;

  TraceNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public ResultFormulaType makeNumber(long number) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("makeNumber(%s)", number),
        () -> delegate.makeNumber(number));
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger number) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("makeNumber(new BigInteger(\"%s\"))", number),
        () -> delegate.makeNumber(number));
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("makeVariable(\"%s\")", pVar),
        () -> delegate.makeVariable(pVar));
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType number) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("negate(%s)", logger.toVariable(number)),
        () -> delegate.negate(number));
  }

  @Override
  public ResultFormulaType add(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("add(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.add(number1, number2));
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "sum(%s)",
            FluentIterable.from(operands).transform(logger::toVariable).join(Joiner.on(", "))),
        () -> delegate.sum(operands));
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("subtract(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.subtract(number1, number2));
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType numerator, ParamFormulaType denominator) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "divide(%s, %s)", logger.toVariable(numerator), logger.toVariable(denominator)),
        () -> delegate.divide(numerator, denominator));
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("multiply(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.multiply(number1, number2));
  }

  @Override
  public BooleanFormula equal(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("equal(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.equal(number1, number2));
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "distinct(%s)",
            FluentIterable.from(pNumbers).transform(logger::toVariable).join(Joiner.on(", "))),
        () -> delegate.distinct(pNumbers));
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "greaterThan(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterThan(number1, number2));
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "greaterOrEquals(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("lessThan(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessThan(number1, number2));
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "lessOrEquals(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessOrEquals(number1, number2));
  }

  @Override
  public IntegerFormula floor(ParamFormulaType formula) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("floor(%s)", logger.toVariable(formula)),
        () -> delegate.floor(formula));
  }
}
