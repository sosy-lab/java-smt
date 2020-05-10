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
package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

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
  public @Nullable T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    synchronized (sync) {
      return delegate.addConstraint(pConstraint);
    }
  }

  @Override
  public void push() {
    synchronized (sync) {
      delegate.push();
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

  @Override
  public Model getModel() throws SolverException {
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
  public void close() {
    synchronized (sync) {
      delegate.close();
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
