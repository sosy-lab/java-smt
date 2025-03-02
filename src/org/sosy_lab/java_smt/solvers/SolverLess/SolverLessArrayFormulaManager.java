// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverLessArrayFormulaManager
    extends AbstractArrayFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  public SolverLessArrayFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  protected SolverLessArrayFormulaManager(
      FormulaCreator<DummyFormula, DummyType, DummyEnv, DummyFunction> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  public <T1 extends Formula, T2 extends Formula> T2 select(
      ArrayFormula<T1, T2> pArray, T1 pIndex) {
    return super.select(pArray, pIndex);
  }

  @Override
  protected DummyFormula select(DummyFormula pArray, DummyFormula pIndex) {
    if (pArray.getSecondArrayParameter().getFormulaType().isArray()) {
      return new DummyFormula(
          pArray.getSecondArrayParameter().getFirstArrayParameter(),
          pArray.getSecondArrayParameter().getSecondArrayParameter());
    }
    return pArray.getSecondArrayParameter();
  }

  @Override
  protected DummyFormula store(DummyFormula pArray, DummyFormula pIndex, DummyFormula pValue) {
    return new DummyFormula(pIndex, pValue);
  }

  @Override
  protected <T1 extends Formula, T2 extends Formula> DummyFormula internalMakeArray(
      String pName, FormulaType<T1> pIndexType, FormulaType<T2> pElementType) {
    DummyFormula result =
        new DummyFormula(
            DummyFormula.getDummyFormulaFromObject(pIndexType),
            DummyFormula.getDummyFormulaFromObject(pElementType));
    result.setName(pName);
    return result;
  }

  @Override
  protected DummyFormula equivalence(DummyFormula pArray1, DummyFormula pArray2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }
}
