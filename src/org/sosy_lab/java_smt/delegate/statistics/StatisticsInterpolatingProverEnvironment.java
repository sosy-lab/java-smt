// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.delegate.statistics.TimerPool.TimerWrapper;

class StatisticsInterpolatingProverEnvironment<T> extends StatisticsBasicProverEnvironment<T>
    implements InterpolatingProverEnvironment<T> {

  private final InterpolatingProverEnvironment<T> delegate;
  private final TimerWrapper itpTimer;

  StatisticsInterpolatingProverEnvironment(
      InterpolatingProverEnvironment<T> pDelegate, SolverStatistics pStats) {
    super(pDelegate, pStats);
    delegate = pDelegate;
    itpTimer = stats.interpolation.getNewTimer();
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    itpTimer.start();
    try {
      return delegate.getInterpolant(pFormulasOfA);
    } finally {
      itpTimer.stop();
    }
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    itpTimer.start();
    try {
      return delegate.getSeqInterpolants(pPartitionedFormulas);
    } finally {
      itpTimer.stop();
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    itpTimer.start();
    try {
      return delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
    } finally {
      itpTimer.stop();
    }
  }
}
