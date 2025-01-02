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
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public abstract class SolverLessNumeralFormulaManager <T extends NumeralFormula,
    Y extends NumeralFormula> extends AbstractNumeralFormulaManager<DummyFormula,
    FormulaTypesForChecking, DummyEnv, T, Y, DummyFunction> {
  public SolverLessNumeralFormulaManager(SolverLessFormulaCreator creator) {
    super(creator, NonLinearArithmetic.APPROXIMATE_FALLBACK);
  }

  @Override
  protected boolean isNumeral(DummyFormula val) {
    return val.getFormulaType() == FormulaTypesForChecking.INTEGER || val.getFormulaType() == FormulaTypesForChecking.RATIONAL;
  }

  @Override
  protected DummyFormula negate(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getFormulaType());
  }

  @Override
  protected DummyFormula add(DummyFormula pParam1, DummyFormula pParam2) {
    if(pParam1.getFormulaType() == FormulaTypesForChecking.RATIONAL
        || pParam2.getFormulaType() == FormulaTypesForChecking.RATIONAL) {
      return new DummyFormula(FormulaTypesForChecking.RATIONAL);
    }
    return new DummyFormula(FormulaTypesForChecking.INTEGER);
  }

  @Override
  protected DummyFormula subtract(DummyFormula pParam1, DummyFormula pParam2) {
    if(pParam1.getFormulaType() == FormulaTypesForChecking.RATIONAL
        || pParam2.getFormulaType() == FormulaTypesForChecking.RATIONAL) {
      return new DummyFormula(FormulaTypesForChecking.RATIONAL);
    }
    return new DummyFormula(FormulaTypesForChecking.INTEGER);
  }

  @Override
  protected DummyFormula equal(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula distinctImpl(List<DummyFormula> pNumbers) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula greaterOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }
}

