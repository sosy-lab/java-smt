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
package org.sosy_lab.solver.basicimpl.cache;

import com.google.common.collect.ImmutableList;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Map;
import java.util.Optional;

import javax.annotation.Nullable;

/**
 * Caching wrapper for an optimizing SMT solver.
 */
public class CachingOptimizationProverEnvironment implements OptimizationProverEnvironment {

  /**
   * Cache: shared between all prover instances.
   * // TODO: cache eviction strategy.
   */
  private final Map<OptimizationQuery, OptimizationResult> optimizationCache;

  /**
   * Copy of the current solver stack.
   */
  private final Deque<OptimizationQuery> stack;

  /**
   * Real optimization environment.
   */
  private final OptimizationProverEnvironment delegate;

  private final OptimizationCacheStatistics statistics;

  /**
   * Current set of constraints and objectives posed to the solver.
   */
  private transient OptimizationQuery currentQuery = OptimizationQuery.empty();

  private transient boolean checkPerformed;

  public CachingOptimizationProverEnvironment(
      OptimizationProverEnvironment pDelegate,
      Map<OptimizationQuery, OptimizationResult> pCache,
      OptimizationCacheStatistics pStatistics) {
    delegate = pDelegate;
    optimizationCache = pCache;
    statistics = pStatistics;
    stack = new ArrayDeque<>();
    checkPerformed = false;
  }

  @Override
  public int maximize(Formula objective) {
    checkPerformed = false;
    int handle = delegate.maximize(objective);
    currentQuery = currentQuery.addObjective(OptimizationObjective.maxObjective(objective), handle);
    return handle;
  }

  @Override
  public int minimize(Formula objective) {
    checkPerformed = false;
    int handle = delegate.maximize(objective);
    currentQuery = currentQuery.addObjective(OptimizationObjective.minObjective(objective), handle);
    return handle;
  }

  @Nullable
  @Override
  public Void addConstraint(BooleanFormula constraint) {
    checkPerformed = false;
    currentQuery = currentQuery.addConstraint(constraint);
    return delegate.addConstraint(constraint);
  }

  @Nullable
  @Override
  public Void push(BooleanFormula f) {
    checkPerformed = false;
    Void out = addConstraint(f);
    push();
    return out;
  }

  @Override
  public void push() {
    checkPerformed = false;
    stack.push(currentQuery);
    delegate.push();
  }

  @Override
  public void pop() {
    checkPerformed = false;
    currentQuery = stack.pop();
    delegate.pop();
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    OptimizationResult cachedResult = optimizationCache.get(currentQuery);
    statistics.incChecks();
    if (cachedResult != null) {
      statistics.incCacheHits();
      return cachedResult.result();
    }
    OptStatus out = delegate.check();
    checkPerformed = true;
    optimizationCache.put(currentQuery, OptimizationResult.of(out));
    return out;
  }

  private OptStatus forceCheck() {
    try {
      return delegate.check();
    } catch (InterruptedException | SolverException pE) {
      throw new UnsupportedOperationException("Solver exception", pE);
    } finally {
      checkPerformed = true;
    }
  }

  @Override
  public java.util.Optional<Rational> upper(int handle, Rational epsilon) {
    OptimizationResult cachedResult = optimizationCache.get(currentQuery);

    // Previous call to {@code check} must create the cached result.
    assert cachedResult != null;
    if (epsilon.equals(Rational.ZERO) && cachedResult.objectiveValues().containsKey(handle)) {
      return cachedResult.objectiveValues().get(handle);
    }
    if (!checkPerformed) {
      forceCheck();
    }
    Optional<Rational> out = delegate.upper(handle, epsilon);
    optimizationCache.put(currentQuery, cachedResult.withObjectiveValue(handle, out));

    return out;
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {

    // TODO: remove the code duplication.
    // TODO: upper vs. lower?
    OptimizationResult cachedResult = optimizationCache.get(currentQuery);

    // Previous call to {@code check} must create the cached result.
    assert cachedResult != null;
    if (epsilon.equals(Rational.ZERO) && cachedResult.objectiveValues().containsKey(handle)) {
      return cachedResult.objectiveValues().get(handle);
    }
    if (!checkPerformed) {
      forceCheck();
    }
    Optional<Rational> out = delegate.lower(handle, epsilon);
    optimizationCache.put(currentQuery, cachedResult.withObjectiveValue(handle, out));
    return out;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return check() == OptStatus.UNSAT;
  }

  @Override
  @SuppressWarnings("resource")
  public Model getModel() throws SolverException {
    OptimizationResult cachedResult = optimizationCache.get(currentQuery);
    assert cachedResult != null;

    if (cachedResult.model().isPresent()) {
      return cachedResult.model().get();
    }

    // If the previous check call was cached, yet no model is available, we would need
    // to re-compute the check.
    if (!checkPerformed) {
      forceCheck();
    }

    Model model = delegate.getModel();
    CachedModel cachedModel = new CachedModel(model);
    optimizationCache.put(currentQuery, cachedResult.withModel(cachedModel));
    return cachedModel;
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    return ImmutableList.copyOf(getModel().iterator());
  }

  @Override
  public String toString() {
    return delegate.toString();
  }

  @Override
  public void close() {
    delegate.close();
  }
}
