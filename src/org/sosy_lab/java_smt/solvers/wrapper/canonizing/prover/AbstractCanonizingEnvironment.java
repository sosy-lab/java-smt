/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.canonizing.prover;

import com.google.common.collect.ImmutableList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormulaVisitor;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public abstract class AbstractCanonizingEnvironment<T> implements BasicProverEnvironment<T> {

  protected FormulaManager fmgr;
  protected CanonizingFormulaVisitor visitor;

  public AbstractCanonizingEnvironment(FormulaManager pMgr, List<CanonizingStrategy> pStrategies) {
    fmgr = pMgr;
    visitor = new CanonizingFormulaVisitor(fmgr, pStrategies);
  }

  protected abstract BasicProverEnvironment<T> getDelegate();

  @Override
  public void pop() {
    visitor.pop();
    getDelegate().pop();
  }

  @Override
  @Nullable
  public T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    fmgr.visit(pConstraint, visitor);
    return getDelegate().addConstraint(visitor.getStorage().getFormula());
  }

  @Override
  public void push() {
    visitor.push();
    getDelegate().push();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return getDelegate().isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    return getDelegate().isUnsatWithAssumptions(pAssumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return getDelegate().getModel();
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    return getDelegate().getModelAssignments();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return getDelegate().getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>>
      unsatCoreOverAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    return getDelegate().unsatCoreOverAssumptions(pAssumptions);
      }

  @Override
  public void close() {
    getDelegate().close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    return getDelegate().allSat(pCallback, pImportant);
      }

}
