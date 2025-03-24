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
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class StatisticsQuantifiedFormulaManager implements QuantifiedFormulaManager {

  private final QuantifiedFormulaManager delegate;
  private final SolverStatistics stats;
  ProverOptions[] option;

  StatisticsQuantifiedFormulaManager(QuantifiedFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier pQ, List<? extends Formula> pVariables, BooleanFormula pBody) {
    stats.quantifierOperations.getAndIncrement();
    return delegate.mkQuantifier(pQ, pVariables, pBody);
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    stats.quantifierOperations.getAndIncrement();
    return delegate.eliminateQuantifiers(pF);
  }

  @Override
  public void setOptions(ProverOptions... opt) {
    option = opt;
  }
}
