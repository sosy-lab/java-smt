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

import static com.google.common.base.Preconditions.checkArgument;
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
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UserPropagator;

/**
 * Common delegate that hands all operations of {@link BasicProverEnvironment} to its delegate. The
 * benefit of using this, is that as long as all nested delegates extend this class, the {@link
 * AbstractProver} is always reachable, for example to perform checks based on it. The delegate
 * needs to be able to provide an {@link AbstractProver} eventually. This class can be extended with
 * more specialized delegate handling, for example: {@link InterpolatingProverDelegateWithChecks},
 * or extended to add handling for the methods of {@link BasicProverEnvironment}, for example:
 * {@link BasicProverWithAssumptionsWrapper}.
 */
abstract class AbstractProverDelegate<T, P extends BasicProverEnvironment<T>>
    implements BasicProverEnvironment<T> {

  protected final P delegate;

  AbstractProverDelegate(P pDelegateProver) {
    checkArgument(
        pDelegateProver instanceof AbstractProver<?>
            || pDelegateProver instanceof AbstractProverDelegate<?, ?>);
    delegate = checkNotNull(pDelegateProver);
  }

  /**
   * @return the {@link AbstractProver} below the delegate, possibly through multiple nested {@link
   *     AbstractProverDelegate} implementations.
   */
  @SuppressWarnings("unchecked")
  AbstractProver<?> getDelegateAsAbstractProver() {
    if (delegate instanceof AbstractProverDelegate<?, ?> nestedProverDelegate) {
      return nestedProverDelegate.getDelegateAsAbstractProver();
    }
    return (AbstractProver<T>) delegate;
  }

  /* ########################## Delegate methods of ProverEnvironment ########################## */
  @Override
  public void pop() {
    delegate.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    delegate.push();
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return delegate.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return delegate.getModel();
  }

  @Override
  public Evaluator getEvaluator() throws SolverException {
    return delegate.getEvaluator();
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
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
  public ImmutableMap<String, String> getStatistics() {
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return delegate.allSat(callback, important);
  }

  @Override
  public boolean registerUserPropagator(UserPropagator propagator) {
    return delegate.registerUserPropagator(propagator);
  }
}
