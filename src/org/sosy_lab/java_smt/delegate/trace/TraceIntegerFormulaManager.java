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
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class TraceIntegerFormulaManager implements IntegerFormulaManager {
  private final IntegerFormulaManager delegate;
  private final TraceLogger logger;

  TraceIntegerFormulaManager(IntegerFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "modularCongruence(%s, %s, new BigInteger(\"%s\"))",
            logger.toVariable(number1), logger.toVariable(number2), n),
        () -> delegate.modularCongruence(number1, number2, n));
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "modularCongruence(%s, %s, %s)",
            logger.toVariable(number1), logger.toVariable(number2), n),
        () -> delegate.modularCongruence(number1, number2, n));
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denominator) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "modulo(%s, %s)", logger.toVariable(numerator), logger.toVariable(denominator)),
        () -> delegate.modulo(numerator, denominator));
  }

  @Override
  public IntegerFormula makeNumber(long number) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("makeNumber(%s)", number),
        () -> delegate.makeNumber(number));
  }

  @Override
  public IntegerFormula makeNumber(BigInteger number) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("makeNumber(new BigInteger(\"%s\"))", number),
        () -> delegate.makeNumber(number));
  }

  @Override
  public IntegerFormula makeNumber(double number) {
    throw new UnsupportedOperationException();
  }

  @Override
  public IntegerFormula makeNumber(BigDecimal number) {
    throw new UnsupportedOperationException();
  }

  @Override
  public IntegerFormula makeNumber(String pI) {
    return makeNumber(new BigInteger(pI));
  }

  @Override
  public IntegerFormula makeNumber(Rational pRational) {
    throw new UnsupportedOperationException();
  }

  @Override
  public IntegerFormula makeVariable(String pVar) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("makeVariable(\"%s\")", pVar),
        () -> delegate.makeVariable(pVar));
  }

  @Override
  public IntegerFormula negate(IntegerFormula number) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("negate(%s)", logger.toVariable(number)),
        () -> delegate.negate(number));
  }

  @Override
  public IntegerFormula add(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("add(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.add(number1, number2));
  }

  @Override
  public IntegerFormula sum(List<IntegerFormula> operands) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "sum(%s)",
            FluentIterable.from(operands).transform(logger::toVariable).join(Joiner.on(", "))),
        () -> delegate.sum(operands));
  }

  @Override
  public IntegerFormula subtract(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("subtract(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.subtract(number1, number2));
  }

  @Override
  public IntegerFormula divide(IntegerFormula numerator, IntegerFormula denominator) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "divide(%s, %s)", logger.toVariable(numerator), logger.toVariable(denominator)),
        () -> delegate.divide(numerator, denominator));
  }

  @Override
  public IntegerFormula multiply(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("multiply(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.multiply(number1, number2));
  }

  @Override
  public BooleanFormula equal(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("equal(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.equal(number1, number2));
  }

  @Override
  public BooleanFormula distinct(List<IntegerFormula> pNumbers) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "distinct(%s)",
            FluentIterable.from(pNumbers).transform(logger::toVariable).join(Joiner.on(", "))),
        () -> delegate.distinct(pNumbers));
  }

  @Override
  public BooleanFormula greaterThan(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "greaterThan(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterThan(number1, number2));
  }

  @Override
  public BooleanFormula greaterOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "greaterOrEquals(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.greaterOrEquals(number1, number2));
  }

  @Override
  public BooleanFormula lessThan(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format("lessThan(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessThan(number1, number2));
  }

  @Override
  public BooleanFormula lessOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return logger.logDef(
        "mgr.getIntegerFormulaManager()",
        String.format(
            "lessOrEquals(%s, %s)", logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.lessOrEquals(number1, number2));
  }

  @Override
  public IntegerFormula floor(IntegerFormula formula) {
    throw new UnsupportedOperationException();
  }
}
