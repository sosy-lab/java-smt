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
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessRationalFormulaManager extends SolverLessNumeralFormulaManager<NumeralFormula,
    RationalFormula>
    implements RationalFormulaManager {

  public SolverLessRationalFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }


  @Override
  protected DummyFormula makeNumberImpl(long i) {
    return new DummyFormula(FormulaTypesForChecking.RATIONAL, Long.toString(i));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigInteger i) {
    return new DummyFormula(FormulaTypesForChecking.RATIONAL, i.toString());
  }

  @Override
  protected DummyFormula makeNumberImpl(String i) {
    return new DummyFormula(FormulaTypesForChecking.RATIONAL, i);
  }

  @Override
  protected DummyFormula makeNumberImpl(double pNumber) {
    return new DummyFormula(FormulaTypesForChecking.RATIONAL, Double.toString(pNumber));
  }
  @Override
  protected DummyFormula makeNumberImpl(BigDecimal pNumber) {
    return new DummyFormula(FormulaTypesForChecking.RATIONAL, pNumber.toPlainString());
  }

  @Override
  protected DummyFormula makeVariableImpl(String i) {
    DummyFormula result = new DummyFormula(FormulaTypesForChecking.RATIONAL);
    result.setName(i);
    return result;

  }
  @Override
  public IntegerFormula floor(NumeralFormula number) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER);
  }
  @Override
  public FormulaType<RationalFormula> getFormulaType() {
    return FormulaType.RationalType;
  }
}
