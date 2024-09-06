// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class StatisticsArrayFormulaManager implements ArrayFormulaManager {

  private final ArrayFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsArrayFormulaManager(ArrayFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {
    stats.arrayOperations.getAndIncrement();
    return delegate.select(pArray, pIndex);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    stats.arrayOperations.getAndIncrement();
    return delegate.store(pArray, pIndex, pValue);
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    stats.arrayOperations.getAndIncrement();
    return delegate.makeArray(pName, pIndexType, pElementType);
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType, TE defaultElement) {
    stats.arrayOperations.getAndIncrement();
    return delegate.makeArray(pIndexType, pElementType, defaultElement);
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    stats.arrayOperations.getAndIncrement();
    return delegate.equivalence(pArray1, pArray2);
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    return delegate.getIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    return delegate.getElementType(pArray);
  }
}
