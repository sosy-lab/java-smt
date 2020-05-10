/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
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
}
