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

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessIntegerFormulaManager extends SolverLessNumeralFormulaManager<IntegerFormula,
    IntegerFormula>
    implements IntegerFormulaManager{

  public SolverLessIntegerFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }


  @Override
  protected DummyFormula makeNumberImpl(long i) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER, String.valueOf(i));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigInteger i) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER, String.valueOf(i));
  }

  @Override
  protected DummyFormula makeNumberImpl(String i) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER,i);
  }

  @Override
  protected DummyFormula makeNumberImpl(double pNumber) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER, String.valueOf(pNumber));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigDecimal pNumber) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER, String.valueOf(pNumber));
  }

  @Override
  protected DummyFormula makeVariableImpl(String i) {

    DummyFormula result = new DummyFormula(FormulaTypesForChecking.INTEGER);
    result.setName(i);
    return result;
  }

  @Override
  protected DummyFormula add(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER);
  }

  @Override
  protected DummyFormula subtract(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER);
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }
}
