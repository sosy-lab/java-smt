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
package org.sosy_lab.java_smt.solvers.wrapper.caching.prover;

import com.google.common.collect.ImmutableList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Stack;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache.CachingMode;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractCachingEnvironment<T> implements BasicProverEnvironment<T> {

  protected BasicProverEnvironment<T> delegate;
  protected BooleanFormulaManager fmgr;
  protected SMTCache cache;
  protected BooleanFormula formula;
  protected Stack<BooleanFormula> stack;

  public AbstractCachingEnvironment(
      BasicProverEnvironment<T> pEnv,
      FormulaManager pMgr,
      CachingMode pMode) {
    delegate = pEnv;
    fmgr = pMgr.getBooleanFormulaManager();
    cache = SMTCache.newSMTCache(pMode);

    formula = fmgr.makeTrue();
    stack = new Stack<>();
    stack.push(formula);
  }

  @Override
  public void pop() {
    formula = stack.pop();
    delegate.pop();
  }

  @Override
  @Nullable
  public T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    formula = fmgr.and(formula, pConstraint);
    return delegate.addConstraint(pConstraint);
  }

  @Override
  public void push() {
    stack.push(formula);
    delegate.push();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Boolean cached = cache.isFormulaUnsat(formula);
    if (cached == null) {
      cached = delegate.isUnsat();
      cache.storeFormulaUnsat(formula, cached);
    }
    return cached;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    Boolean cached = cache.isFormulaUnsatWithAssumptions(formula, pAssumptions);
    if (cached == null) {
      cached = delegate.isUnsatWithAssumptions(pAssumptions);
      cache.storeFormulaUnsatWithAssumptions(formula, cached, pAssumptions);
    }
    return cached;
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Model cached = cache.getFormulaModel(formula);
    if (cached == null) {
      cached = delegate.getModel();
      cache.storeFormulaModel(formula, cached);
    }
    return cached;
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    ImmutableList<ValueAssignment> cached = cache.getFormulaModelAssignments(formula);
    if (cached == null) {
      cached = delegate.getModelAssignments();
      cache.storeFormulaModelAssignments(formula, cached);
    }
    return cached;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    List<BooleanFormula> cached = cache.getFormulaUnsatCore(formula);
    if (cached == null) {
      cached = delegate.getUnsatCore();
      cache.storeFormulaUnsatCore(formula, cached);
    }
    return cached;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
        Optional<List<BooleanFormula>> cached =
            cache.getFormulaUnsatCoreOverAssumptions(formula, pAssumptions);
        if (cached == null || !cached.isPresent()) {
          cached = delegate.unsatCoreOverAssumptions(pAssumptions);
          cache.storeFormulaUnsatCoreOverAssumptions(formula, cached, pAssumptions);
        }
        return cached;
      }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
        return delegate.allSat(pCallback, pImportant);
      }
}
