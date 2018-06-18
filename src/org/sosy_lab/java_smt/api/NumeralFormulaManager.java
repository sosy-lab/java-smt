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
package org.sosy_lab.java_smt.api;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;

/**
 * This interface represents the Numeral Theory.
 *
 * @param <ParamFormulaType> formulaType of the parameters
 * @param <ResultFormulaType> formulaType of arithmetic results
 */
public interface NumeralFormulaManager<
    ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula> {

  ResultFormulaType makeNumber(long number);

  ResultFormulaType makeNumber(BigInteger number);

  /**
   * Create a numeric literal with a given value. Note: if the theory represented by this instance
   * cannot handle rational numbers, the value may get rounded or otherwise represented imprecisely.
   */
  ResultFormulaType makeNumber(double number);

  /**
   * Create a numeric literal with a given value. Note: if the theory represented by this instance
   * cannot handle rational numbers, the value may get rounded or otherwise represented imprecisely.
   */
  ResultFormulaType makeNumber(BigDecimal number);

  ResultFormulaType makeNumber(String pI);

  ResultFormulaType makeNumber(Rational pRational);

  /**
   * Creates a variable with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  ResultFormulaType makeVariable(String pVar);

  FormulaType<ResultFormulaType> getFormulaType();

  // ----------------- Arithmetic relations, return type NumeralFormula -----------------

  ResultFormulaType negate(ParamFormulaType number);

  ResultFormulaType add(ParamFormulaType number1, ParamFormulaType number2);

  ResultFormulaType sum(List<ParamFormulaType> operands);

  ResultFormulaType subtract(ParamFormulaType number1, ParamFormulaType number2);

  ResultFormulaType divide(ParamFormulaType number1, ParamFormulaType number2);

  ResultFormulaType modulo(ParamFormulaType number1, ParamFormulaType number2);

  ResultFormulaType multiply(ParamFormulaType number1, ParamFormulaType number2);

  // ----------------- Numeric relations, return type BooleanFormula -----------------

  BooleanFormula equal(ParamFormulaType number1, ParamFormulaType number2);

  BooleanFormula greaterThan(ParamFormulaType number1, ParamFormulaType number2);

  BooleanFormula greaterOrEquals(ParamFormulaType number1, ParamFormulaType number2);

  BooleanFormula lessThan(ParamFormulaType number1, ParamFormulaType number2);

  BooleanFormula lessOrEquals(ParamFormulaType number1, ParamFormulaType number2);
}
