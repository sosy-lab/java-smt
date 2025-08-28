// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
class StatisticsNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {

  private final NumeralFormulaManager<ParamFormulaType, ResultFormulaType> delegate;
  final SolverStatistics stats;

  StatisticsNumeralFormulaManager(
      NumeralFormulaManager<ParamFormulaType, ResultFormulaType> pDelegate,
      SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public ResultFormulaType makeNumber(long pNumber) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeNumber(pNumber);
  }

  @Override
  public ResultFormulaType makeNumber(BigInteger pNumber) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeNumber(pNumber);
  }

  @Override
  public ResultFormulaType makeNumber(double pNumber) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeNumber(pNumber);
  }

  @Override
  public ResultFormulaType makeNumber(BigDecimal pNumber) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeNumber(pNumber);
  }

  @Override
  public ResultFormulaType makeNumber(String pI) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeNumber(pI);
  }

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeNumber(pRational);
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    stats.numericOperations.getAndIncrement();
    return delegate.makeVariable(pVar);
  }

  @Override
  public FormulaType<ResultFormulaType> getFormulaType() {
    stats.numericOperations.getAndIncrement();
    return delegate.getFormulaType();
  }

  @Override
  public ResultFormulaType negate(ParamFormulaType pNumber) {
    stats.numericOperations.getAndIncrement();
    return delegate.negate(pNumber);
  }

  @Override
  public ResultFormulaType add(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.add(pNumber1, pNumber2);
  }

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> pOperands) {
    stats.numericOperations.getAndIncrement();
    return delegate.sum(pOperands);
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.subtract(pNumber1, pNumber2);
  }

  @Override
  public ResultFormulaType divide(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.divide(pNumber1, pNumber2);
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.multiply(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula equal(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.equal(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    stats.numericOperations.getAndIncrement();
    return delegate.distinct(pNumbers);
  }

  @Override
  public BooleanFormula greaterThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.greaterThan(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.greaterOrEquals(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula lessThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.lessThan(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.lessOrEquals(pNumber1, pNumber2);
  }

  @Override
  public IntegerFormula floor(ParamFormulaType pNumber) {
    stats.numericOperations.getAndIncrement();
    return delegate.floor(pNumber);
  }

  @Override
  public RationalFormula toRational(ParamFormulaType formula) {
    stats.numericOperations.getAndIncrement();
    return delegate.toRational(formula);
  }
}
