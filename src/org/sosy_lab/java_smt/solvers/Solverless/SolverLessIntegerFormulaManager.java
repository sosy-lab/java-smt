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

package org.sosy_lab.java_smt.solvers.Solverless;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
public class SolverLessIntegerFormulaManager extends SolverLessNumeralFormulaManager<IntegerFormula,
    IntegerFormula>
    implements IntegerFormulaManager{

  public SolverLessIntegerFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  BooleanFormula dummyBooleanFormula = new BooleanFormula() {
  };
  IntegerFormula dummyIntegerFormula = new IntegerFormula() {
  };

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1,
      IntegerFormula number2,
      BigInteger n) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    return dummyBooleanFormula;
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denumerator) {
    return dummyIntegerFormula;
  }

  @Override
  public IntegerFormula negate(IntegerFormula number) {
    return dummyIntegerFormula;
  }

  @Override
  public IntegerFormula add(IntegerFormula number1, IntegerFormula number2) {
    return dummyIntegerFormula;
  }

  @Override
  public IntegerFormula sum(List<IntegerFormula> operands) {
    return dummyIntegerFormula;
  }

  @Override
  public IntegerFormula subtract(IntegerFormula number1, IntegerFormula number2) {
    return dummyIntegerFormula;
  }

  @Override
  public IntegerFormula divide(IntegerFormula numerator, IntegerFormula denumerator) {
    return dummyIntegerFormula;
  }

  @Override
  public IntegerFormula multiply(IntegerFormula number1, IntegerFormula number2) {
    return dummyIntegerFormula;
  }

  @Override
  public BooleanFormula equal(IntegerFormula number1, IntegerFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula distinct(List<IntegerFormula> pNumbers) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula greaterThan(IntegerFormula number1, IntegerFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula greaterOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula lessThan(IntegerFormula number1, IntegerFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula lessOrEquals(IntegerFormula number1, IntegerFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public IntegerFormula floor(IntegerFormula formula) {
    return dummyIntegerFormula;
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }
}
