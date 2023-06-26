/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.apron;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class ApronIntegerFormulaManager extends ApronNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {
  protected ApronIntegerFormulaManager(
      FormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1,
      IntegerFormula number2,
      BigInteger n) {
    return null;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    return null;
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denumerator) {
    return null;
  }

  @Override
  public IntegerFormula makeNumber(long number) {
    return null;
  }

  @Override
  public IntegerFormula makeNumber(BigInteger number) {
    return null;
  }

  @Override
  public IntegerFormula makeNumber(double number) {
    return null;
  }

  @Override
  public IntegerFormula makeNumber(BigDecimal number) {
    return null;
  }

  @Override
  public IntegerFormula makeNumber(String pI) {
    return null;
  }

  @Override
  public IntegerFormula makeNumber(Rational pRational) {
    return null;
  }

  @Override
  public IntegerFormula makeVariable(String pVar) {
    return null;
  }

  @Override
  public IntegerFormula negate(IntegerFormula number) {
    return null;
  }

  @Override
  public IntegerFormula add(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public IntegerFormula sum(List operands) {
    return null;
  }

  @Override
  public IntegerFormula subtract(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public IntegerFormula divide(IntegerFormula numerator, IntegerFormula denumerator) {
    return null;
  }

  @Override
  public IntegerFormula multiply(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula equal(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula distinct(List pNumbers) {
    return null;
  }

  @Override
  public BooleanFormula greaterThan(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula greaterOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula lessThan(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula lessOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return null;
  }

  @Override
  public IntegerFormula floor(IntegerFormula formula) {
    return null;
  }
}
