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

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

public class SolverLessArrayFormulaManager extends AbstractArrayFormulaManager<DummyFormula,
    DummyType, DummyEnv, DummyFunction> {
  public SolverLessArrayFormulaManager() {
    super(new SolverLessFormulaCreator());
  }
  @Override
  protected DummyFormula select(DummyFormula pArray, DummyFormula pIndex) {
    return null;
  }

  @Override
  protected DummyFormula store(DummyFormula pArray, DummyFormula pIndex, DummyFormula pValue) {
    return null;
  }

  @Override
  protected <TI extends Formula, TE extends Formula> DummyFormula internalMakeArray(
      String pName,
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType) {
    return null;
  }

  @Override
  protected DummyFormula equivalence(DummyFormula pArray1, DummyFormula pArray2) {
    return null;
  }
}
