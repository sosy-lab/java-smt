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
package org.sosy_lab.solver.reusableStack;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;

abstract class ReusableStackAbstractProver<T, D extends BasicProverEnvironment<T>>
    implements BasicProverEnvironment<T> {

  D delegate;
  private int size;

  ReusableStackAbstractProver(D pDelegate) {
    delegate = checkNotNull(pDelegate);
    delegate.push(); // create initial empty level that can be popped on close().
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(size >= 0);
    return delegate.isUnsat();
  }

  @Override
  public final void push() {
    size++;
    delegate.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(size > 0);
    size--;
    delegate.pop();
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(size >= 0);
    return delegate.getModel();
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(size >= 0);
    return delegate.getModelAssignments();
  }

  @Override
  public void close() {
    while (size > 0) {
      pop();
    }
    Preconditions.checkState(size == 0);
    delegate.pop(); // remove initial level
    delegate.close();
  }
}
