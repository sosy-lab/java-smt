// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public class DebuggingArrayFormulaManager implements ArrayFormulaManager {
  private final ArrayFormulaManager delegate;
  private final DebuggingSolverContext debugging;

  public DebuggingArrayFormulaManager(
      ArrayFormulaManager pDelegate, DebuggingSolverContext pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pArray);
    debugging.assertFormulaInContext(pIndex);
    TE result = delegate.select(pArray, pIndex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pArray);
    debugging.assertFormulaInContext(pIndex);
    debugging.assertFormulaInContext(pValue);
    ArrayFormula<TI, TE> result = delegate.store(pArray, pIndex, pValue);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    debugging.assertThreadLocal();
    ArrayFormula<TI, TE> result = delegate.makeArray(pName, pIndexType, pElementType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName, ArrayFormulaType<TI, TE> type) {
    debugging.assertThreadLocal();
    ArrayFormula<TI, TE> result = delegate.makeArray(pName, type);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType, TE elseElem) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(elseElem);
    ArrayFormula<TI, TE> result = delegate.makeArray(pIndexType, pElementType, elseElem);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pArray1);
    debugging.assertFormulaInContext(pArray2);
    BooleanFormula result = delegate.equivalence(pArray1, pArray2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pArray);
    return delegate.getIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pArray);
    return delegate.getElementType(pArray);
  }
}
