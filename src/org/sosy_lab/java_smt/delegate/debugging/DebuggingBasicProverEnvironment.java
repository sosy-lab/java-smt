// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UserPropagator;

class DebuggingBasicProverEnvironment<T> implements BasicProverEnvironment<T> {
  private final BasicProverEnvironment<T> delegate;
  private final DebuggingAssertions debugging;

  DebuggingBasicProverEnvironment(
      BasicProverEnvironment<T> pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public @Nullable T push(BooleanFormula f) throws InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f);
    return delegate.push(f);
  }

  @Override
  public void pop() {
    debugging.assertThreadLocal();
    delegate.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(constraint);
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    debugging.assertThreadLocal();
    delegate.push();
  }

  @Override
  public int size() {
    debugging.assertThreadLocal();
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    for (BooleanFormula f : assumptions) {
      debugging.assertFormulaInContext(f);
    }
    return delegate.isUnsatWithAssumptions(assumptions);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    debugging.assertThreadLocal();
    return new DebuggingModel(delegate.getModel(), debugging);
  }

  @SuppressWarnings("resource")
  @Override
  public Evaluator getEvaluator() throws SolverException {
    debugging.assertThreadLocal();
    return new DebuggingEvaluator(delegate.getEvaluator(), debugging);
  }

  @Override
  public ImmutableList<Model.ValueAssignment> getModelAssignments() throws SolverException {
    debugging.assertThreadLocal();
    ImmutableList<Model.ValueAssignment> result = delegate.getModelAssignments();
    for (Model.ValueAssignment v : result) {
      // Both lines are needed as assignments like "a == false" may have been simplified to
      // "not(a)" by the solver. This then leads to errors as the term "false" is not defined in
      // the context.
      debugging.addFormulaTerm(v.getValueAsFormula());
      debugging.addFormulaTerm(v.getAssignmentAsFormula());
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    debugging.assertThreadLocal();
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    for (BooleanFormula f : assumptions) {
      debugging.assertFormulaInContext(f);
    }
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    debugging.assertThreadLocal();
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    debugging.assertThreadLocal();
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    debugging.assertThreadLocal();
    for (BooleanFormula f : important) {
      debugging.assertFormulaInContext(f);
    }
    return delegate.allSat(callback, important);
  }

  @Override
  public boolean registerUserPropagator(UserPropagator propagator) {
    throw new UnsupportedOperationException();
  }
}
