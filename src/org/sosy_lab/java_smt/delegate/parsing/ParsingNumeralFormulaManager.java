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
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
public abstract class ParsingNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {
  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;

  private final ParsingFormulaManager.Declarations declarations;

  ParsingNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate,
      ParsingFormulaManager.Declarations pDeclarations) {
    declarations = pDeclarations;
    delegate = pDelegate;
  }

  @Override
  public ResultFormulaType makeNumber(long number) {
    return delegate.makeNumber(number);
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger number) {
    return delegate.makeNumber(number);
  }

  @Override
  public ResultFormulaType makeNumber(double number) {
    return delegate.makeNumber(number);
  }

  @Override
  public ResultFormulaType makeNumber(BigDecimal number) {
    return delegate.makeNumber(number);
  }

  @Override
  public ResultFormulaType makeNumber(String pI) {
    return delegate.makeNumber(pI);
  }

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    return delegate.makeNumber(pRational);
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    ResultFormulaType term = delegate.makeVariable(pVar);
    declarations.addConstant(pVar, term);
    return term;
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType number) {
    return delegate.negate(number);
  }

  @Override
  public ResultFormulaType add(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.add(number1, number2);
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    return delegate.sum(operands);
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.subtract(number1, number2);
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType numerator, ParamFormulaType denominator) {
    return delegate.divide(numerator, denominator);
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.multiply(number1, number2);
  }

  @Override
  public BooleanFormula equal(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.equal(number1, number2);
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    return delegate.distinct(pNumbers);
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.greaterThan(number1, number2);
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.greaterOrEquals(number1, number2);
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.lessThan(number1, number2);
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    return delegate.lessOrEquals(number1, number2);
  }

  @Override
  public NumeralFormula.IntegerFormula floor(ParamFormulaType formula) {
    return delegate.floor(formula);
  }
}
