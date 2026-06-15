/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

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
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UserPropagator;

/**
 * Delegate for all methods in {@link BasicProverEnvironment} (including the ones with default
 * impls) with common checks for them based on methods provided through the delegated {@link
 * AbstractProver}.
 */
abstract class AbstractProverDelegateWithChecks<T, P extends BasicProverEnvironment<T>>
    extends AbstractProverDelegate<T, P> {

  AbstractProverDelegateWithChecks(P pDelegateProver) {
    super(pDelegateProver);
  }

  @SuppressWarnings("resource")
  @Override
  public void pop() {
    getDelegateAsAbstractProver().checkProverState();
    delegate.pop();
  }

  @SuppressWarnings("resource")
  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.addConstraint(constraint);
  }

  @SuppressWarnings("resource")
  @Override
  public void push() throws InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    delegate.push();
  }

  @SuppressWarnings("resource")
  @Override
  public int size() {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.size();
  }

  @SuppressWarnings("resource")
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.isUnsat();
  }

  @SuppressWarnings("resource")
  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.isUnsatWithAssumptions(assumptions);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.getModel();
  }

  @SuppressWarnings("resource")
  @Override
  public Evaluator getEvaluator() throws SolverException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.getEvaluator();
  }

  @SuppressWarnings("resource")
  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.getModelAssignments();
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getUnsatCore() {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.getUnsatCore();
  }

  @SuppressWarnings("resource")
  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @SuppressWarnings("resource")
  @Override
  public ImmutableMap<String, String> getStatistics() {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.getStatistics();
  }

  @SuppressWarnings("resource")
  @Override
  public void close() {
    delegate.close();
  }

  @SuppressWarnings("resource")
  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.allSat(callback, important);
  }

  @SuppressWarnings("resource")
  @Override
  public boolean registerUserPropagator(UserPropagator propagator) {
    getDelegateAsAbstractProver().checkProverState();
    return delegate.registerUserPropagator(propagator);
  }
}
