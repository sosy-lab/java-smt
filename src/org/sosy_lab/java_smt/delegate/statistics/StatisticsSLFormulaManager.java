// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class StatisticsSLFormulaManager implements SLFormulaManager {

  private final SLFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsSLFormulaManager(SLFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula pF1, BooleanFormula pF2) {
    stats.slOperations.getAndIncrement();
    return delegate.makeStar(pF1, pF2);
  }

  @Override
  public <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF pPtr, VF pTo) {
    stats.slOperations.getAndIncrement();
    return delegate.makePointsTo(pPtr, pTo);
  }

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula pF1, BooleanFormula pF2) {
    stats.slOperations.getAndIncrement();
    return delegate.makeMagicWand(pF1, pF2);
  }

  @Override
  public <
          AF extends Formula,
          VF extends Formula,
          AT extends FormulaType<AF>,
          VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType) {
    stats.slOperations.getAndIncrement();
    return delegate.makeEmptyHeap(pAdressType, pValueType);
  }

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType) {
    stats.slOperations.getAndIncrement();
    return delegate.makeNilElement(pAdressType);
  }
}
