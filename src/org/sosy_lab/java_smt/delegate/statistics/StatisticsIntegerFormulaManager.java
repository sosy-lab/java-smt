// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class StatisticsIntegerFormulaManager
    extends StatisticsNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  private final IntegerFormulaManager delegate;

  StatisticsIntegerFormulaManager(IntegerFormulaManager pDelegate, SolverStatistics pStats) {
    super(pDelegate, pStats);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula pNumber1, IntegerFormula pNumber2, BigInteger pN) {
    stats.numericOperations.getAndIncrement();
    return delegate.modularCongruence(pNumber1, pNumber2, pN);
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula pNumber1, IntegerFormula pNumber2, long pN) {
    stats.numericOperations.getAndIncrement();
    return delegate.modularCongruence(pNumber1, pNumber2, pN);
  }

  @Override
  public IntegerFormula modulo(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    stats.numericOperations.getAndIncrement();
    return delegate.modulo(pNumber1, pNumber2);
  }
}
