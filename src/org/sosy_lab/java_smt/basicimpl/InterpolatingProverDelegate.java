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

  private final InterpolatingProverEnvironment<T> itpProver;

  InterpolatingProverDelegate(InterpolatingProverEnvironment<T> pBaseProver) {
    itpProver = checkNotNull(pBaseProver);
  }

  @SuppressWarnings("resource")
  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkGenerateInterpolants(formulasOfA);
    // TODO: do we want a common method to calculate partition B out of the asserted formulas
    //  efficiently? We currently have several distinct solutions.
    return itpProver.getInterpolant(formulasOfA);
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver().checkGenerateSeqInterpolants(partitionedFormulas);
    // TODO: problem/inefficiency; unsupported solvers still check validity of input before failing?
    return itpProver.getSeqInterpolants(partitionedFormulas);
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    getDelegateAsAbstractProver()
        .checkGenerateTreeInterpolants(partitionedFormulas, startOfSubTree);
    // TODO: problem/inefficiency; unsupported solvers still check validity of input before failing?
    return itpProver.getTreeInterpolants(partitionedFormulas, startOfSubTree);
  }

  /* ########################## Delegate methods of ProverEnvironment ########################## */

  @Override
  public void pop() {
    itpProver.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    return itpProver.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    itpProver.push();
  }

  @Override
  public int size() {
    return itpProver.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return itpProver.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return itpProver.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return itpProver.getModel();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return itpProver.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return itpProver.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    itpProver.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return itpProver.allSat(callback, important);
  }

  /* ############################### Utility methods ############################### */
  @SuppressWarnings("unchecked")
  private AbstractProver<T> getDelegateAsAbstractProver() {
    return (AbstractProver<T>) itpProver;
  }
}
