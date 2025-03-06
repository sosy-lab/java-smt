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
    extends AbstractArrayFormulaManager<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  public SolverLessArrayFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  protected SolverLessArrayFormulaManager(
      FormulaCreator<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  public <T1 extends Formula, T2 extends Formula> T2 select(
      ArrayFormula<T1, T2> pArray, T1 pIndex) {
    return super.select(pArray, pIndex);
  }

  @Override
  protected SMTLIB2Formula select(SMTLIB2Formula pArray, SMTLIB2Formula pIndex) {
    if (pArray.getSecondArrayParameter().getFormulaType().isArray()) {
      return new SMTLIB2Formula(
          pArray.getSecondArrayParameter().getFirstArrayParameter(),
          pArray.getSecondArrayParameter().getSecondArrayParameter());
    }
    return pArray.getSecondArrayParameter();
  }

  @Override
  protected SMTLIB2Formula store(
      SMTLIB2Formula pArray, SMTLIB2Formula pIndex, SMTLIB2Formula pValue) {
    SMTLIB2Formula result = new SMTLIB2Formula(pIndex, pValue);
    result.setName(pArray.getName());
    return result;
  }

  @Override
  protected <T1 extends Formula, T2 extends Formula> SMTLIB2Formula internalMakeArray(
      String pName, FormulaType<T1> pIndexType, FormulaType<T2> pElementType) {
    SMTLIB2Formula result =
        new SMTLIB2Formula(
            SMTLIB2Formula.getDummyFormulaFromObject(pIndexType),
            SMTLIB2Formula.getDummyFormulaFromObject(pElementType));
    result.setName(pName);
    return result;
  }

  @Override
  protected <T1 extends Formula, T2 extends Formula> SMTLIB2Formula internalMakeArray(
      FormulaType<T1> pIndexType, FormulaType<T2> pElementType, SMTLIB2Formula elseElem) {
    return new SMTLIB2Formula(
        SMTLIB2Formula.getDummyFormulaFromObject(pIndexType),
        SMTLIB2Formula.getDummyFormulaFromObject(pElementType));
  }

  @Override
  protected SMTLIB2Formula equivalence(SMTLIB2Formula pArray1, SMTLIB2Formula pArray2) {
    return new SMTLIB2Formula(pArray1.equals(pArray2));
  }
}
