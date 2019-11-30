/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.basicimpl.reusableStack;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;

abstract class ReusableStackAbstractProver<T, D extends BasicProverEnvironment<T>>
    implements BasicProverEnvironment<T> {

  D delegate;

  /**
   * track size of nested stack.
   *
   * <p>Size=1 indicates a first level on the nested stack and provides an empty stack for users.
   */
  private int size;

  ReusableStackAbstractProver(D pDelegate) {
    delegate = checkNotNull(pDelegate);
    delegate.push(); // create initial empty level that can be popped on close().
    size++;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(size >= 1);
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    return delegate.isUnsatWithAssumptions(pAssumptions);
  }

  @Override
  public final void push() {
    size++;
    delegate.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(size > 1);
    size--;
    delegate.pop();
  }

  @Override
  public T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    return delegate.addConstraint(pConstraint);
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(size >= 1);
    return delegate.getModel();
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(size >= 1);
    return delegate.getModelAssignments();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    while (size > 1) {
      pop();
    }
    if (size == 1) {
      delegate.pop(); // remove initial level
      size--;
      delegate.close();
    } else {
      Preconditions.checkState(size == 0);
    }
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return delegate.allSat(callback, important);
  }
}
