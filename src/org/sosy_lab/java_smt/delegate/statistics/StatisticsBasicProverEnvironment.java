/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
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
  public void pop() {
    stats.pop.getAndIncrement();
    delegate.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    stats.constraint.getAndIncrement();
    return delegate.addConstraint(pConstraint);
  }

  @Override
  public void push() {
    stats.push.getAndIncrement();
    delegate.push();
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
  public Model getModel() throws SolverException {
    stats.model.getAndIncrement();
    return new StatisticsModel(delegate.getModel(), stats);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
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
