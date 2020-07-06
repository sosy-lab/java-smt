// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class SynchronizedSLFormulaManager implements SLFormulaManager {

  private final SLFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedSLFormulaManager(SLFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula pF1, BooleanFormula pF2) {
    synchronized (sync) {
      return delegate.makeStar(pF1, pF2);
    }
  }

  @Override
  public <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF pPtr, VF pTo) {
    synchronized (sync) {
      return delegate.makePointsTo(pPtr, pTo);
    }
  }

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula pF1, BooleanFormula pF2) {
    synchronized (sync) {
      return delegate.makeMagicWand(pF1, pF2);
    }
  }

  @Override
  public <
          AF extends Formula,
          VF extends Formula,
          AT extends FormulaType<AF>,
          VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType) {
    synchronized (sync) {
      return delegate.makeEmptyHeap(pAdressType, pValueType);
    }
  }

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType) {
    synchronized (sync) {
      return delegate.makeNilElement(pAdressType);
    }
  }
}
