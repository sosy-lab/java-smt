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

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This delegate enables common implementations for methods in {@link
 * InterpolatingProverEnvironment} based on the implementations in the abstract/theorem prover that
 * can not be done using abstract implementations.
 */
class InterpolatingProverDelegate<T> implements InterpolatingProverEnvironment<T> {

  InterpolatingProverEnvironment<T> baseInterpolatingProver;

  InterpolatingProverDelegate(InterpolatingProverEnvironment<T> pBaseProver) {
    baseInterpolatingProver = checkNotNull(pBaseProver);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    // TODO: add common checks/preconditions
    return baseInterpolatingProver.getInterpolant(formulasOfA);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    // TODO: add common checks/preconditions
    return baseInterpolatingProver.getSeqInterpolants(partitionedFormulas);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    // TODO: add common checks/preconditions
    return baseInterpolatingProver.getTreeInterpolants(partitionedFormulas, startOfSubTree);
  }

  /* ########################## Delegate methods of ProverEnvironment ########################## */

  @Override
  public void pop() {
    baseInterpolatingProver.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    return baseInterpolatingProver.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    baseInterpolatingProver.push();
  }

  @Override
  public int size() {
    return baseInterpolatingProver.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return baseInterpolatingProver.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return baseInterpolatingProver.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return baseInterpolatingProver.getModel();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return baseInterpolatingProver.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return baseInterpolatingProver.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    baseInterpolatingProver.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return baseInterpolatingProver.allSat(callback, important);
  }
}
