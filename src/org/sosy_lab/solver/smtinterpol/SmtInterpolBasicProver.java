/*
 *
 *  *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  *  This file is part of JavaSMT.
 *  *
 *  *  Copyright (C) 2007-2016  Dirk Beyer
 *  *  All rights reserved.
 *  *
 *  *  Licensed under the Apache License, Version 2.0 (the "License");
 *  *  you may not use this file except in compliance with the License.
 *  *  You may obtain a copy of the License at
 *  *
 *  *      http://www.apache.org/licenses/LICENSE-2.0
 *  *
 *  *  Unless required by applicable law or agreed to in writing, software
 *  *  distributed under the License is distributed on an "AS IS" BASIS,
 *  *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  *  See the License for the specific language governing permissions and
 *  *  limitations under the License.
 *
 *
 */

package org.sosy_lab.solver.smtinterpol;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.CanIgnoreReturnValue;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.Collection;

public abstract class SmtInterpolBasicProver<T> implements BasicProverEnvironment<T> {

  private boolean closed = false;
  private final SmtInterpolEnvironment env;
  private final FormulaCreator<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> creator;

  private static final String PREFIX = "term_"; // for termnames
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different termnames

  SmtInterpolBasicProver(SmtInterpolFormulaManager pMgr) {
    env = pMgr.createEnvironment();
    creator = pMgr.getFormulaCreator();
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    env.push(1);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    env.pop(1);
  }

  @Override
  @CanIgnoreReturnValue
  public T push(BooleanFormula f) {
    push();
    return addConstraint(f);
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    Preconditions.checkState(!closed);
    return !env.checkSat();
  }

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    return new SmtInterpolModel(env.getModel(), creator, getAssertedTerms());
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (Model model = getModel()) {
      return ImmutableList.copyOf(model);
    }
  }

  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  protected abstract Collection<Term> getAssertedTerms();

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    closed = true;
  }
}
