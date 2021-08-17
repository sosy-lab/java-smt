// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

class StatisticsStringFormulaManager implements StringFormulaManager {

  private final StringFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsStringFormulaManager(StringFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public StringFormula makeString(String value) {
    stats.stringOperations.getAndIncrement();
    return delegate.makeString(value);
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    stats.stringOperations.getAndIncrement();
    return delegate.makeVariable(pVar);
  }

  @Override
  public StringFormula equal(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.equal(str1, str2);
  }
}
