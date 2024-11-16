// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

class SynchronizedBasicProverEnvironment<T> implements BasicProverEnvironment<T> {

  private final BasicProverEnvironment<T> delegate;
  final SolverContext sync;

  SynchronizedBasicProverEnvironment(BasicProverEnvironment<T> pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public void pop() {
    synchronized (sync) {
      delegate.pop();
    }
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula pConstraint)
      throws InterruptedException, SolverException {
    synchronized (sync) {
      return delegate.addConstraint(pConstraint);
    }
  }

  @Override
  public void push() throws InterruptedException, SolverException {
    synchronized (sync) {
      delegate.push();
    }
  }

  @Override
  public int size() {
    synchronized (sync) {
      return delegate.size();
    }
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    synchronized (sync) {
      return delegate.isUnsat();
    }
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    synchronized (sync) {
      return delegate.isUnsatWithAssumptions(pAssumptions);
    }
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException, InterruptedException {
    synchronized (sync) {
      return new SynchronizedModel(delegate.getModel(), sync);
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    synchronized (sync) {
      return delegate.getUnsatCore();
    }
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    synchronized (sync) {
      return delegate.unsatCoreOverAssumptions(pAssumptions);
    }
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    synchronized (sync) {
      return delegate.getStatistics();
    }
  }

  @Override
  public void close() {
    synchronized (sync) {
      delegate.close();
    }
  }

  @Override
  public String toString() {
    synchronized (sync) {
      return delegate.toString();
    }
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    synchronized (sync) {
      return delegate.allSat(pCallback, pImportant);
    }
  }
}
