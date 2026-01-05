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
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager.SymbolManager;

public class ParsingIntegerFormulaManager implements IntegerFormulaManager {
  private final SymbolManager symbolManager;
  private final IntegerFormulaManager delegate;

  public ParsingIntegerFormulaManager(
      SymbolManager pSymbolManager, IntegerFormulaManager pDelegate) {
    symbolManager = pSymbolManager;
    delegate = pDelegate;
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    return delegate.modularCongruence(number1, number2, n);
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    return delegate.modularCongruence(number1, number2, n);
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denominator) {
    return delegate.modulo(numerator, denominator);
  }

  @Override
  public IntegerFormula makeNumber(long number) {
    return delegate.makeNumber(number);
  }

  @Override
  public IntegerFormula makeNumber(BigInteger number) {
    return delegate.makeNumber(number);
  }

  @Override
  public IntegerFormula makeNumber(double number) {
    return delegate.makeNumber(number);
  }

  @Override
  public IntegerFormula makeNumber(BigDecimal number) {
    return delegate.makeNumber(number);
  }

  @Override
  public IntegerFormula makeNumber(String pI) {
    return delegate.makeNumber(pI);
  }

  @Override
  public IntegerFormula makeNumber(Rational pRational) {
    return delegate.makeNumber(pRational);
  }

  @Override
  public IntegerFormula makeVariable(String pVar) {
    var term = delegate.makeVariable(pVar);
    symbolManager.addConstant(pVar, term);
    return term;
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return delegate.getFormulaType();
  }

  @Override
  public IntegerFormula negate(IntegerFormula number) {
    return delegate.negate(number);
  }

  @Override
  public IntegerFormula add(IntegerFormula number1, IntegerFormula number2) {
    return delegate.add(number1, number2);
  }

  @Override
  public IntegerFormula sum(List<IntegerFormula> operands) {
    return delegate.sum(operands);
  }

  @Override
  public IntegerFormula subtract(IntegerFormula number1, IntegerFormula number2) {
    return delegate.subtract(number1, number2);
  }

  @Override
  public IntegerFormula divide(IntegerFormula numerator, IntegerFormula denominator) {
    return delegate.divide(numerator, denominator);
  }

  @Override
  public IntegerFormula multiply(IntegerFormula number1, IntegerFormula number2) {
    return delegate.multiply(number1, number2);
  }

  @Override
  public BooleanFormula equal(IntegerFormula number1, IntegerFormula number2) {
    return delegate.equal(number1, number2);
  }

  @Override
  public BooleanFormula distinct(List<IntegerFormula> pNumbers) {
    return delegate.distinct(pNumbers);
  }

  @Override
  public BooleanFormula greaterThan(IntegerFormula number1, IntegerFormula number2) {
    return delegate.greaterThan(number1, number2);
  }

  @Override
  public BooleanFormula greaterOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return delegate.greaterOrEquals(number1, number2);
  }

  @Override
  public BooleanFormula lessThan(IntegerFormula number1, IntegerFormula number2) {
    return delegate.lessThan(number1, number2);
  }

  @Override
  public BooleanFormula lessOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return delegate.lessOrEquals(number1, number2);
  }

  @Override
  public IntegerFormula floor(IntegerFormula formula) {
    return delegate.floor(formula);
  }
}
