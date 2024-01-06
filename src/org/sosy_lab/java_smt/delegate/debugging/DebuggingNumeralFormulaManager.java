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
import org.sosy_lab.java_smt.delegate.debugging.DebuggingSolverContext.NodeManager;

@SuppressWarnings("ClassTypeParameterName")
public class DebuggingNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends FormulaChecks implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {
  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;

  public DebuggingNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate,
      NodeManager pformulasInContext) {
    super(pformulasInContext);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public ResultFormulaType makeNumber(long number) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger number) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(double number) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(BigDecimal number) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(String pI) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(pI);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeNumber(pRational);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    assertThreadLocal();
    ResultFormulaType result = delegate.makeVariable(pVar);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public FormulaType<ResultFormulaType> getFormulaType() {
    assertThreadLocal();
    return delegate.getFormulaType();
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    ResultFormulaType result = delegate.negate(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType add(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    ResultFormulaType result = delegate.add(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    assertThreadLocal();
    for (ParamFormulaType t : operands) {
      assertFormulaInContext(t);
    }
    ResultFormulaType result = delegate.sum(operands);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    ResultFormulaType result = delegate.subtract(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType numerator, ParamFormulaType denumerator) {
    assertThreadLocal();
    assertFormulaInContext(numerator);
    assertFormulaInContext(denumerator);
    ResultFormulaType result = delegate.divide(numerator, denumerator);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    ResultFormulaType result = delegate.multiply(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula equal(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.equal(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    assertThreadLocal();
    for (ParamFormulaType t : pNumbers) {
      assertFormulaInContext(t);
    }
    BooleanFormula result = delegate.distinct(pNumbers);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterThan(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterOrEquals(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessThan(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType number1, ParamFormulaType number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessOrEquals(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public IntegerFormula floor(ParamFormulaType formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    IntegerFormula result = delegate.floor(formula);
    addFormulaToContext(result);
    return result;
  }
}
