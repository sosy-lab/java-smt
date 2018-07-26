/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper;

import com.google.common.collect.ImmutableList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import javax.annotation.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class CanonizingOptimizationEnvironmentWrapper implements OptimizationProverEnvironment {

  private OptimizationProverEnvironment delegate;
  private FormulaManager fmgr;
  private CanonizingFormulaVisitor visitor;

  public CanonizingOptimizationEnvironmentWrapper(
      OptimizationProverEnvironment pEnv, FormulaManager pFormulaManager) {
    delegate = pEnv;
    fmgr = pFormulaManager;
    visitor = new CanonizingFormulaVisitor(fmgr);
  }

  @Override
  public void pop() {
    visitor.pop();
    delegate.pop();
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    fmgr.visit(pConstraint, visitor);
    delegate.addConstraint(visitor.getStorage().getFormula());
    return null;
  }

  @Override
  public void push() {
    visitor.push();
    delegate.push();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    return delegate.isUnsatWithAssumptions(pAssumptions);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    ImmutableList<ValueAssignment> assignments = delegate.getModelAssignments();
    // TODO translate back
    return assignments;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    List<BooleanFormula> unsatCore = delegate.getUnsatCore();
    // TODO translate back
    return unsatCore;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    Optional<List<BooleanFormula>> unsatCore = delegate.unsatCoreOverAssumptions(pAssumptions);
    if (unsatCore.isPresent()) {
      // TODO translate back
    }
    return unsatCore;
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public int maximize(Formula pObjective) {
    return delegate.maximize(pObjective);
  }

  @Override
  public int minimize(Formula pObjective) {
    return delegate.minimize(pObjective);
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    return delegate.check();
  }

  @Override
  public Optional<Rational> upper(int pHandle, Rational pEpsilon) {
    return delegate.upper(pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> lower(int pHandle, Rational pEpsilon) {
    return delegate.lower(pHandle, pEpsilon);
  }

  @Override
  public Model getModel() throws SolverException {
    return new CanonizingModel(delegate.getModel());
  }
}
