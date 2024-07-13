// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

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
public class DebuggingNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {
  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;
  private final DebuggingAssertions debugging;

  public DebuggingNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate,
      DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public ResultFormulaType makeNumber(long number) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger number) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(double number) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(BigDecimal number) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(String pI) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(pI);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(pRational);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    debugging.assertThreadLocal();
    ResultFormulaType result = delegate.makeVariable(pVar);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public FormulaType<ResultFormulaType> getFormulaType() {
    debugging.assertThreadLocal();
    return delegate.getFormulaType();
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    ResultFormulaType result = delegate.negate(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType add(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    ResultFormulaType result = delegate.add(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    debugging.assertThreadLocal();
    for (ParamFormulaType t : operands) {
      debugging.assertFormulaInContext(t);
    }
    ResultFormulaType result = delegate.sum(operands);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    ResultFormulaType result = delegate.subtract(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType numerator, ParamFormulaType denominator) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(numerator);
    debugging.assertFormulaInContext(denominator);
    ResultFormulaType result = delegate.divide(numerator, denominator);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    ResultFormulaType result = delegate.multiply(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula equal(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.equal(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    debugging.assertThreadLocal();
    for (ParamFormulaType t : pNumbers) {
      debugging.assertFormulaInContext(t);
    }
    BooleanFormula result = delegate.distinct(pNumbers);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterThan(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterOrEquals(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessThan(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessOrEquals(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula floor(ParamFormulaType formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    IntegerFormula result = delegate.floor(formula);
    debugging.addFormulaTerm(result);
    return result;
  }
}
