// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.delegate.statistics.TimerPool.TimerWrapper;

class StatisticsBasicProverEnvironment<T> implements BasicProverEnvironment<T> {

  private final BasicProverEnvironment<T> delegate;
  final SolverStatistics stats;
  final TimerWrapper unsatTimer;
  private final TimerWrapper allSatTimer;

  StatisticsBasicProverEnvironment(BasicProverEnvironment<T> pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
    unsatTimer = stats.unsat.getNewTimer();
    allSatTimer = stats.allSat.getNewTimer();
    stats.provers.getAndIncrement();
  }

  @Override
  public void pop() throws InterruptedException {
    stats.pop.getAndIncrement();
    delegate.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula pConstraint)
      throws InterruptedException, SolverException {
    stats.constraint.getAndIncrement();
    return delegate.addConstraint(pConstraint);
  }

  @Override
  public void push() throws InterruptedException, SolverException {
    stats.push.getAndIncrement();
    delegate.push();
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    unsatTimer.start();
    try {
      return delegate.isUnsat();
    } finally {
      unsatTimer.stop();
    }
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    unsatTimer.start();
    try {
      return delegate.isUnsatWithAssumptions(pAssumptions);
    } finally {
      unsatTimer.stop();
    }
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException, InterruptedException {
    stats.model.getAndIncrement();
    return new StatisticsModel(delegate.getModel(), stats);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments()
      throws SolverException, InterruptedException {
    return delegate.getModelAssignments();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() throws InterruptedException {
    stats.unsatCore.getAndIncrement();
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    stats.unsatCore.getAndIncrement();
    return delegate.unsatCoreOverAssumptions(pAssumptions);
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public String toString() {
    return delegate.toString();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    allSatTimer.start();
    try {
      return delegate.allSat(pCallback, pImportant);
    } finally {
      allSatTimer.stop();
    }
  }
}
