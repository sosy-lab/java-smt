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

import com.google.common.collect.Maps;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
class InterpolatingProverDelegate<T> implements InterpolatingProverEnvironment<Integer> {

  private final InterpolatingProverEnvironment<T> itpProver;

  private Map<Integer, T> assertionIds = new HashMap<>();
  private int lastId = 0;

  InterpolatingProverDelegate(InterpolatingProverEnvironment<T> pBaseProver) {
    checkArgument(pBaseProver instanceof AbstractProver<?>);
    itpProver = checkNotNull(pBaseProver);
  }

  @SuppressWarnings("resource")
  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA)
      throws SolverException, InterruptedException {
    Collection<T> formulaIds = formulasOfA.stream().map(assertionIds::get).toList();
    getDelegateAsAbstractProver().checkGenerateInterpolants(formulaIds);
    // TODO: do we want a common method to calculate partition B out of the asserted formulas
    //  efficiently? We currently have several distinct solutions.
    return itpProver.getInterpolant(formulaIds);
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas)
      throws SolverException, InterruptedException {
    List<? extends Collection<T>> partitionedFormulaIds =
        partitionedFormulas.stream()
            .map(partition -> partition.stream().map(assertionIds::get).toList())
            .toList();
    getDelegateAsAbstractProver().checkGenerateSeqInterpolants(partitionedFormulaIds);
    // TODO: problem/inefficiency; unsupported solvers still check validity of input before failing?
    return itpProver.getSeqInterpolants(partitionedFormulaIds);
  }

  @SuppressWarnings("resource")
  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    List<? extends Collection<T>> partitionedFormulaIds =
        partitionedFormulas.stream()
            .map(partition -> partition.stream().map(assertionIds::get).toList())
            .toList();
    getDelegateAsAbstractProver()
        .checkGenerateTreeInterpolants(partitionedFormulaIds, startOfSubTree);
    // TODO: problem/inefficiency; unsupported solvers still check validity of input before failing?
    return itpProver.getTreeInterpolants(partitionedFormulaIds, startOfSubTree);
  }

  /* ########################## Delegate methods of ProverEnvironment ########################## */

  @SuppressWarnings("resource")
  @Override
  public void pop() {
    itpProver.pop();
    lastId = getDelegateAsAbstractProver().getAssertedConstraintIds().size();
    assertionIds = new HashMap<>(Maps.filterKeys(assertionIds, k -> k <= lastId));
  }

  @Override
  public @Nullable Integer addConstraint(BooleanFormula constraint) throws InterruptedException {
    var newId = ++lastId;
    assertionIds.put(newId, itpProver.addConstraint(constraint));
    return newId;
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
