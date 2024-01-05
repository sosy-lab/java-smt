// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Set;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public class DebuggingArrayFormulaManager extends FormulaChecks implements ArrayFormulaManager {
  private final ArrayFormulaManager delegate;

  public DebuggingArrayFormulaManager(ArrayFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {
    assertThreadLocal();
    assertFormulaInContext(pArray);
    assertFormulaInContext(pIndex);
    TE result = delegate.select(pArray, pIndex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    assertThreadLocal();
    assertFormulaInContext(pArray);
    assertFormulaInContext(pIndex);
    assertFormulaInContext(pValue);
    ArrayFormula<TI, TE> result = delegate.store(pArray, pIndex, pValue);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    assertThreadLocal();
    ArrayFormula<TI, TE> result = delegate.makeArray(pName, pIndexType, pElementType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName, ArrayFormulaType<TI, TE> type) {
    assertThreadLocal();
    ArrayFormula<TI, TE> result = delegate.makeArray(pName, type);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    assertThreadLocal();
    assertFormulaInContext(pArray1);
    assertFormulaInContext(pArray2);
    BooleanFormula result = delegate.equivalence(pArray1, pArray2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    assertThreadLocal();
    assertFormulaInContext(pArray);
    return delegate.getIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    assertThreadLocal();
    assertFormulaInContext(pArray);
    return delegate.getElementType(pArray);
  }
}
