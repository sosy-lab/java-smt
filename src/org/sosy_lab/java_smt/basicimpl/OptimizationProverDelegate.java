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

import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This delegate enables common implementations for methods in {@link OptimizationProverEnvironment}
 * based on the implementations in the abstract/theorem prover that can not be done using abstract
 * implementations.
 */
public class OptimizationProverDelegate implements OptimizationProverEnvironment {

  private final OptimizationProverEnvironment optimizationProver;

  OptimizationProverDelegate(OptimizationProverEnvironment pBaseProver) {
    checkArgument(pBaseProver instanceof AbstractProver<?>);
    optimizationProver = checkNotNull(pBaseProver);
  }

  @SuppressWarnings("resource")
  @Override
  public int maximize(Formula objective) throws InterruptedException {
    getDelegateAsAbstractProver().checkClosed();
    getDelegateAsAbstractProver().shutdownIfNecessary();
    return optimizationProver.maximize(objective);
  }

  @SuppressWarnings("resource")
  @Override
  public int minimize(Formula objective) throws InterruptedException {
    getDelegateAsAbstractProver().checkClosed();
    getDelegateAsAbstractProver().shutdownIfNecessary();
    return optimizationProver.minimize(objective);
  }

  @SuppressWarnings("resource")
  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) throws InterruptedException {
    getDelegateAsAbstractProver().checkGenerateModels();
    getDelegateAsAbstractProver().shutdownIfNecessary();
    return optimizationProver.upper(handle, epsilon);
  }

  @SuppressWarnings("resource")
  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) throws InterruptedException {
    getDelegateAsAbstractProver().checkGenerateModels();
    getDelegateAsAbstractProver().shutdownIfNecessary();
    return optimizationProver.lower(handle, epsilon);
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    // We don't need to do anything for check, as it is already handled in AbstractProver
    return optimizationProver.check();
  }

  /* ########################## Delegate methods of ProverEnvironment ########################## */

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException, InterruptedException {
    // TODO: add checks here?
    return optimizationProver.getModel();
  }

  @Override
  public void pop() throws InterruptedException {
    optimizationProver.pop();
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint) throws InterruptedException {
    return optimizationProver.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    optimizationProver.push();
  }

  @Override
  public int size() {
    return optimizationProver.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return optimizationProver.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return optimizationProver.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() throws InterruptedException {
    return optimizationProver.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return optimizationProver.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public ImmutableMap<String, String> getStatistics() throws InterruptedException {
    return optimizationProver.getStatistics();
  }

  @Override
  public void close() {
    optimizationProver.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return optimizationProver.allSat(callback, important);
  }

  /* ############################### Utility methods ############################### */
  @SuppressWarnings("unchecked")
  private AbstractProver<?> getDelegateAsAbstractProver() {
    return (AbstractProver<?>) optimizationProver;
  }
}
