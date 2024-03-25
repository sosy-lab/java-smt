// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.SolverContext;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class SynchronizedArrayFormulaManager implements ArrayFormulaManager {

  private final ArrayFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedArrayFormulaManager(ArrayFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {
    synchronized (sync) {
      return delegate.select(pArray, pIndex);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    synchronized (sync) {
      return delegate.store(pArray, pIndex, pValue);
    }
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    synchronized (sync) {
      return delegate.makeArray(pName, pIndexType, pElementType);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName, ArrayFormulaType<TI, TE> pType) {
    synchronized (sync) {
      return delegate.makeArray(pName, pType);
    }
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType) {
    synchronized (sync) {
      return delegate.makeArray(pIndexType, pElementType);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      ArrayFormulaType<TI, TE> type) {
    synchronized (sync) {
      return delegate.makeArray(type);
    }
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(TE elseElem, FTI pIndexType, FTE pElementType) {
    synchronized (sync) {
      return delegate.makeArray(elseElem, pIndexType, pElementType);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      TE elseElem, ArrayFormulaType<TI, TE> type) {
    synchronized (sync) {
      return delegate.makeArray(elseElem, type);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    synchronized (sync) {
      return delegate.equivalence(pArray1, pArray2);
    }
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    synchronized (sync) {
      return delegate.getIndexType(pArray);
    }
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    synchronized (sync) {
      return delegate.getElementType(pArray);
    }
  }
}
