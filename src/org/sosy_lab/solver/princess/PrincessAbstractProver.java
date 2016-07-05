/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.princess;

import static com.google.common.base.Preconditions.checkNotNull;

import ap.parser.IExpression;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;

abstract class PrincessAbstractProver<E, AF> implements BasicProverEnvironment<E> {

  protected final PrincessStack stack;
  protected final PrincessFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>(); // all terms on all levels

  protected final FormulaCreator<
          IExpression, PrincessTermType, PrincessEnvironment, PrincessFunctionDeclaration>
      creator;
  protected boolean closed = false;

  protected PrincessAbstractProver(
      PrincessFormulaManager pMgr,
      boolean useForInterpolation,
      FormulaCreator<
              IExpression, PrincessTermType, PrincessEnvironment, PrincessFunctionDeclaration>
          creator) {
    this.mgr = pMgr;
    this.creator = creator;
    this.stack = checkNotNull(mgr.getEnvironment().getNewStack(useForInterpolation));
  }

  /** This function causes the SatSolver to check all the terms on the stack,
   * if their conjunction is SAT or UNSAT.
   */
  @Override
  public boolean isUnsat() throws SolverException {
    Preconditions.checkState(!closed);
    return !stack.checkSat();
  }

  @Override
  public final void push() {
    Preconditions.checkState(!closed);
    assertedFormulas.push(new ArrayList<>());
    stack.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.pop();
    stack.pop();
  }

  @Override
  public PrincessModel getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!isUnsat(), "model is only available for SAT environments");
    return new PrincessModel(stack.getPartialModel(), creator);
  }

  protected abstract Collection<? extends IExpression> getAssertedFormulas();

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (PrincessModel model = getModel()) {
      return model.modelToList();
    }
  }

  @Override
  public void close() {
    checkNotNull(stack);
    checkNotNull(mgr);
    if (!closed) {
      stack.close();
    }
    closed = true;
  }
}
