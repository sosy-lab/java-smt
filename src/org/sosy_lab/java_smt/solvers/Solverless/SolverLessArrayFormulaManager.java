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

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.GeneratorException;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessArrayFormulaManager extends AbstractArrayFormulaManager<DummyFormula,
    FormulaTypesForChecking, DummyEnv, DummyFunction> {
  public SolverLessArrayFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  protected SolverLessArrayFormulaManager(FormulaCreator<DummyFormula, FormulaTypesForChecking, DummyEnv, DummyFunction> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray,
      TI pIndex) {
    return super.select(pArray, pIndex);
  }

  @Override
  protected DummyFormula select(DummyFormula pArray, DummyFormula pIndex) {
    return new DummyFormula("", FormulaTypesForChecking.ARRAY);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray,
      TI pIndex,
      TE pValue) {
    return super.store(pArray, pIndex, pValue);
  }

  @Override
  protected DummyFormula store(DummyFormula pArray, DummyFormula pIndex, DummyFormula pValue) {
    return new DummyFormula("", FormulaTypesForChecking.ARRAY);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName,
      ArrayFormulaType<TI, TE> type) throws GeneratorException {
    return super.makeArray(pName, type);
  }

  @Override
  public <TI extends Formula, TE extends Formula, FTI extends FormulaType<TI>, FTE extends FormulaType<TE>> ArrayFormula<TI, TE> makeArray(
      String pName,
      FTI pIndexType,
      FTE pElementType) throws GeneratorException {
    return super.makeArray(pName, pIndexType, pElementType);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> DummyFormula internalMakeArray(
      String pName,
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType) {
    return new DummyFormula("", FormulaTypesForChecking.ARRAY);
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    return super.getIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    return super.getElementType(pArray);
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1,
      ArrayFormula<TI, TE> pArray2) {
    return super.equivalence(pArray1, pArray2);
  }

  @Override
  protected DummyFormula equivalence(DummyFormula pArray1, DummyFormula pArray2) {
    return new DummyFormula("", FormulaTypesForChecking.BOOLEAN);
  }
}
