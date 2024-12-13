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

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class SolverLessRationalFormulaManager extends SolverLessNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {
  RationalFormula dummyRationalFormula = new RationalFormula() {};
  BooleanFormula dummyBooleanFormula = new BooleanFormula() {};

  public SolverLessRationalFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }

  @Override
  public RationalFormula negate(NumeralFormula number) {
    return dummyRationalFormula;
  }

  @Override
  public RationalFormula add(NumeralFormula number1, NumeralFormula number2) {
    return dummyRationalFormula;
  }

  @Override
  public RationalFormula sum(List<NumeralFormula> operands) {
    return dummyRationalFormula;
  }

  @Override
  public RationalFormula subtract(NumeralFormula number1, NumeralFormula number2) {
    return dummyRationalFormula;
  }

  @Override
  public RationalFormula divide(NumeralFormula numerator, NumeralFormula denumerator) {
    return dummyRationalFormula;
  }

  @Override
  public RationalFormula multiply(NumeralFormula number1, NumeralFormula number2) {
    return dummyRationalFormula;
  }

  @Override
  public BooleanFormula equal(NumeralFormula number1, NumeralFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula distinct(List<NumeralFormula> pNumbers) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula greaterThan(NumeralFormula number1, NumeralFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula greaterOrEquals(NumeralFormula number1, NumeralFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula lessThan(NumeralFormula number1, NumeralFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public BooleanFormula lessOrEquals(NumeralFormula number1, NumeralFormula number2) {
    return dummyBooleanFormula;
  }

  @Override
  public IntegerFormula floor(NumeralFormula formula) {
    return new IntegerFormula() {};
  }

  @Override
  public FormulaType<RationalFormula> getFormulaType() {
    return FormulaType.RationalType;
  }
}
