// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

class StatisticsOptimizationProverEnvironment extends StatisticsBasicProverEnvironment<Void>
    implements OptimizationProverEnvironment {

  private final OptimizationProverEnvironment delegate;

  StatisticsOptimizationProverEnvironment(
      OptimizationProverEnvironment pDelegate, SolverStatistics pStats) {
    super(pDelegate, pStats);
    delegate = pDelegate;
  }

  @Override
  public int maximize(Formula pObjective) {
    return delegate.maximize(pObjective);
  }

  @Override
  public int minimize(Formula pObjective) {
    return delegate.minimize(pObjective);
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    unsatTimer.start();
    try {
      return delegate.check();
    } finally {
      unsatTimer.stop();
    }
  }

  @Override
  public Optional<Rational> upper(int pHandle, Rational pEpsilon) {
    return delegate.upper(pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> lower(int pHandle, Rational pEpsilon) {
    return delegate.lower(pHandle, pEpsilon);
  }
}
