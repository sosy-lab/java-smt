// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.UFManager;

class StatisticsUFManager implements UFManager {

  private final UFManager delegate;
  private final SolverStatistics stats;

  StatisticsUFManager(UFManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgs) {
    stats.ufOperations.getAndIncrement();
    return delegate.declareUF(pName, pReturnType, pArgs);
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> pFuncType, List<? extends Formula> pArgs) {
    stats.ufOperations.getAndIncrement();
    return delegate.callUF(pFuncType, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String pName, FormulaType<T> pReturnType, List<Formula> pArgs) {
    stats.ufOperations.getAndIncrement();
    return delegate.declareAndCallUF(pName, pReturnType, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String pName, FormulaType<T> pReturnType, Formula... pArgs) {
    stats.ufOperations.getAndIncrement();
    return delegate.declareAndCallUF(pName, pReturnType, pArgs);
  }
}
