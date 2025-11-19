// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  // flags for option
  protected final boolean generateModels;
  protected final boolean generateAllSat;
  protected final boolean generateUnsatCores;
  private final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;

  // flags for status
  protected boolean closed = false;
  private boolean wasLastSatCheckSatisfiable = true; // assume SAT for an empty prover
  protected boolean changedSinceLastSatQuery = true; // assume changed for an empty prover

  private final Set<Evaluator> evaluators = new LinkedHashSet<>();

  /**
   * This data-structure tracks all formulas that were asserted on different levels. We can assert a
   * formula multiple times on the same or also distinct levels and return a new ID for each
   * assertion.
   */
  private final List<Multimap<BooleanFormula, T>> assertedFormulas = new ArrayList<>();

  private static final String TEMPLATE = "Please set the prover option %s.";

  protected AbstractProver(Set<ProverOptions> pOptions) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateAllSat = pOptions.contains(ProverOptions.GENERATE_ALL_SAT);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    enableSL = pOptions.contains(ProverOptions.ENABLE_SEPARATION_LOGIC);

    assertedFormulas.add(LinkedHashMultimap.create());
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(generateModels, TEMPLATE, ProverOptions.GENERATE_MODELS);
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    Preconditions.checkState(wasLastSatCheckSatisfiable, NO_MODEL_HELP);
  }

  protected final void checkGenerateAllSat() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(generateAllSat, TEMPLATE, ProverOptions.GENERATE_ALL_SAT);
  }

  protected final void checkGenerateUnsatCores() {
    Preconditions.checkState(generateUnsatCores, TEMPLATE, ProverOptions.GENERATE_UNSAT_CORE);
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    Preconditions.checkState(!wasLastSatCheckSatisfiable);
  }

  protected final void checkGenerateUnsatCoresOverAssumptions() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        TEMPLATE,
        ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    Preconditions.checkState(!wasLastSatCheckSatisfiable);
  }

  protected final void checkEnableSeparationLogic() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(enableSL, TEMPLATE, ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  protected abstract boolean hasPersistentModel();

  private void setChanged() {
    wasLastSatCheckSatisfiable = false;
    if (!changedSinceLastSatQuery) {
      changedSinceLastSatQuery = true;
      if (!hasPersistentModel()) {
        closeAllEvaluators();
      }
    }
  }

  @Override
  public int size() {
    checkState(!closed);
    return assertedFormulas.size() - 1;
  }

  @Override
  public final void push() throws InterruptedException {
    checkState(!closed);
    pushImpl();
    setChanged();
    assertedFormulas.add(LinkedHashMultimap.create());
  }

  protected abstract void pushImpl() throws InterruptedException;

  @Override
  public final void pop() {
    checkState(!closed);
    checkState(assertedFormulas.size() > 1, "initial level must remain until close");
    assertedFormulas.remove(assertedFormulas.size() - 1); // remove last
    popImpl();
    setChanged();
  }

  protected abstract void popImpl();

  @Override
  @CanIgnoreReturnValue
  public final @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    checkState(!closed);
    T t = addConstraintImpl(constraint);
    setChanged();
    Iterables.getLast(assertedFormulas).put(constraint, t);
    return t;
  }

  protected abstract @Nullable T addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException;

  /** Check whether the conjunction of all formulas on the stack is unsatisfiable. */
  public final boolean isUnsat() throws SolverException, InterruptedException {
    checkState(!closed);
    changedSinceLastSatQuery = false;
    wasLastSatCheckSatisfiable = false;
    final boolean isUnsat = isUnsatImpl();
    if (!isUnsat) {
      wasLastSatCheckSatisfiable = true;
    }
    return isUnsat;
  }

  protected abstract boolean isUnsatImpl() throws SolverException, InterruptedException;

  /** Override for OptimizationProver */
  public final OptStatus check() throws InterruptedException, SolverException {
    checkState(!closed);
    wasLastSatCheckSatisfiable = false;
    changedSinceLastSatQuery = false;
    final OptStatus status = checkImpl();
    if (status == OptStatus.OPT) {
      wasLastSatCheckSatisfiable = true;
    }
    return status;
  }

  protected OptStatus checkImpl() throws InterruptedException, SolverException {
    if (this instanceof OptimizationProverEnvironment) {
      throw new UnsupportedOperationException("checkImpl() must be implemented in a subclass.");
    }
    throw new UnsupportedOperationException("check() is not supported by this prover.");
  }

  protected ImmutableSet<BooleanFormula> getAssertedFormulas() {
    ImmutableSet.Builder<BooleanFormula> builder = ImmutableSet.builder();
    for (Multimap<BooleanFormula, T> level : assertedFormulas) {
      builder.addAll(level.keySet());
    }
    return builder.build();
  }

  protected ImmutableSet<T> getAssertedConstraintIds() {
    ImmutableSet.Builder<T> builder = ImmutableSet.builder();
    for (Multimap<BooleanFormula, T> level : assertedFormulas) {
      builder.addAll(level.values());
    }
    return builder.build();
  }

  /**
   * This method registers the Evaluator to be cleaned up before the next change on the prover
   * stack.
   */
  protected <E extends Evaluator> E registerEvaluator(E pEvaluator) {
    evaluators.add(pEvaluator);
    return pEvaluator;
  }

  protected void unregisterEvaluator(Evaluator pEvaluator) {
    evaluators.remove(pEvaluator);
  }

  protected void closeAllEvaluators() {
    ImmutableList.copyOf(evaluators).forEach(Evaluator::close);
    evaluators.clear();
  }

  @Override
  public void close() {
    assertedFormulas.clear();
    closeAllEvaluators();
    closed = true;
  }
}
