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
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager.SymbolManager;

public class ParsingRationalFormulaManager implements RationalFormulaManager {
  private final SymbolManager symbolManager;
  private final RationalFormulaManager delegate;

  public ParsingRationalFormulaManager(
      SymbolManager pSymbolManager, RationalFormulaManager pDelegate) {
    symbolManager = pSymbolManager;
    delegate = pDelegate;
  }

  @Override
  public RationalFormula makeNumber(long number) {
    return delegate.makeNumber(number);
  }

  @Override
  public RationalFormula makeNumber(BigInteger number) {
    return delegate.makeNumber(number);
  }

  @Override
  public RationalFormula makeNumber(double number) {
    return delegate.makeNumber(number);
  }

  @Override
  public RationalFormula makeNumber(BigDecimal number) {
    return delegate.makeNumber(number);
  }

  @Override
  public RationalFormula makeNumber(String pI) {
    return delegate.makeNumber(pI);
  }

  @Override
  public RationalFormula makeNumber(Rational pRational) {
    return delegate.makeNumber(pRational);
  }

  @Override
  public RationalFormula makeVariable(String pVar) {
    var term = delegate.makeVariable(pVar);
    symbolManager.addConstant(pVar, term);
    return term;
  }

  @Override
  public FormulaType<RationalFormula> getFormulaType() {
    return delegate.getFormulaType();
  }

  @Override
  public RationalFormula negate(NumeralFormula number) {
    return delegate.negate(number);
  }

  @Override
  public RationalFormula add(NumeralFormula number1, NumeralFormula number2) {
    return delegate.add(number1, number2);
  }

  @Override
  public RationalFormula sum(List<NumeralFormula> operands) {
    return delegate.sum(operands);
  }

  @Override
  public RationalFormula subtract(NumeralFormula number1, NumeralFormula number2) {
    return delegate.subtract(number1, number2);
  }

  @Override
  public RationalFormula divide(NumeralFormula numerator, NumeralFormula denominator) {
    return delegate.divide(numerator, denominator);
  }

  @Override
  public RationalFormula multiply(NumeralFormula number1, NumeralFormula number2) {
    return delegate.multiply(number1, number2);
  }

  @Override
  public BooleanFormula equal(NumeralFormula number1, NumeralFormula number2) {
    return delegate.equal(number1, number2);
  }

  @Override
  public BooleanFormula distinct(List<NumeralFormula> pNumbers) {
    return delegate.distinct(pNumbers);
  }

  @Override
  public BooleanFormula greaterThan(NumeralFormula number1, NumeralFormula number2) {
    return delegate.greaterThan(number1, number2);
  }

  @Override
  public BooleanFormula greaterOrEquals(NumeralFormula number1, NumeralFormula number2) {
    return delegate.greaterOrEquals(number1, number2);
  }

  @Override
  public BooleanFormula lessThan(NumeralFormula number1, NumeralFormula number2) {
    return delegate.lessThan(number1, number2);
  }

  @Override
  public BooleanFormula lessOrEquals(NumeralFormula number1, NumeralFormula number2) {
    return delegate.lessOrEquals(number1, number2);
  }

  @Override
  public IntegerFormula floor(NumeralFormula formula) {
    return delegate.floor(formula);
  }
}
