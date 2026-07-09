// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  // TODO: we could use this in a proper state machine to control the prover
  enum ProverState {
    CLOSED {
      @Override
      public boolean isClosed() {
        return true;
      }
    },

    CHANGED_SINCE_LAST_SAT_QUERY,

    /** Initial state of a prover. We assume that it is SAT, but also that the state is changed. */
    CHANGED_SINCE_LAST_SAT_QUERY_SAT,

    /** The last query was SAT and the prover is unchanged since this was established. */
    UNCHANGED_SAT {
      @Override
      public final boolean lastQueryWasSAT() {
        return true;
      }

      @Override
      public final boolean isUnchangedSinceLastQuery() {
        return true;
      }
    },

    UNCHANGED_UNSAT {
      @Override
      public final boolean lastQueryWasUNSAT() {
        return true;
      }

      @Override
      public final boolean isUnchangedSinceLastQuery() {
        return true;
      }
    };

    /**
     * It is disallowed to call any prover method that requires an unchanged prover state after
     * establishing SAT or UNSAT (for example {@link BasicProverEnvironment#getModel()}, {@link
     * InterpolatingProverEnvironment#getInterpolant(Collection)}, {@link
     * BasicProverEnvironment#getUnsatCore()} etc.) if this method returns {@code false}.
     *
     * @return {@code false} if the prover state changed since the last call to isUnsat() (or other
     *     satisfiability establishing methods) with a valid (SAT/UNSAT) result. {@code true} if the
     *     prover state has not been changed since the last valid result; either SAT or UNSAT.
     */
    public boolean isUnchangedSinceLastQuery() {
      return false;
    }

    /**
     * Can be used to check whether calls to methods that require a SAT result in the last
     * satisfiability check are allowed. All model/evaluator methods require this. For example:
     * {@link BasicProverEnvironment#getModel()} etc.
     *
     * @return {@code true} only if the last satisfiability check returned SAT. {@code false} in all
     *     other cases.
     */
    public boolean lastQueryWasSAT() {
      return false;
    }

    /**
     * Can be used to check whether calls to methods that require a UNSAT result in the last
     * satisfiability check are allowed. Examples for methods that require this: {@link
     * InterpolatingProverEnvironment#getInterpolant(Collection)}, {@link
     * BasicProverEnvironment#getUnsatCore()} etc.
     *
     * @return {@code true} only if the last satisfiability check returned UNSAT. {@code false} in
     *     all other cases.
     */
    public boolean lastQueryWasUNSAT() {
      return false;
    }

    /**
     * @return {@code true} only if the solver is closed. No methods besides {@link #close()} are
     *     allowed to be called anymore if it is closed. A solver can never be "unclosed"!
     */
    public boolean isClosed() {
      return false;
    }
  }

  // flags for option
  protected final boolean generateModels;
  protected final boolean generateAllSat;
  protected final boolean generateUnsatCores;
  protected final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;

  // We assume changed for an empty prover, but it is also SAT (which might not be used!)
  private ProverState proverState = ProverState.CHANGED_SINCE_LAST_SAT_QUERY_SAT;

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

  /** Checks whether the prover has been closed and throws if it is closed. */
  protected void checkNotClosed() {
    checkState(
        !proverState.isClosed(),
        "The prover is already closed. No further operations are permitted.");
  }

  /**
   * @return {@code true} if the prover has been closed and may not be used anymore, {@code false}
   *     else.
   */
  public final boolean isClosed() {
    return proverState.isClosed();
  }

  /**
   * Checks whether operations that require an unchanged prover state since the last satisfiability
   * check (e.g. {@link #isUnsat()}) that returned UNSAT are allowed to be used (e.g.{@link
   * #getUnsatCore()}, {@link InterpolatingProverEnvironment#getInterpolant(Collection)} etc.).
   * Throws if the prover state has been modified (e.g. via {@link #push()}, {@link #pop()} etc.) or
   * the last result was not UNSAT.
   */
  protected void checkUnchangedSinceLastQueryUnsatisfiable() {
    checkState(
        proverState.isUnchangedSinceLastQuery(),
        "The prover state changed since the last satisfiability check. The called method may only"
            + " be used directly after a satisfiability check returned UNSAT.");
    checkState(
        proverState.lastQueryWasUNSAT(),
        "The last query was not satisfiable. The called method may only be used directly after a"
            + " satisfiability check returned UNSAT.");
  }

  /**
   * Checks whether operations that require an unchanged prover state since the last satisfiability
   * check (e.g. {@link #isUnsat()}) that returned SAT are allowed to be used (e.g.{@link
   * #getModel()}, {@link #getEvaluator()}, {@link OptimizationProverEnvironment#upper(int,
   * Rational)} etc.). Throws if the prover state has been modified (e.g. via {@link #push()},
   * {@link #pop()} etc.) or the last result was not SAT.
   */
  protected void checkUnchangedSinceLastQuerySatisfiable() {
    checkState(
        proverState.isUnchangedSinceLastQuery(),
        "The prover state changed since the last satisfiability check. The called method may only"
            + " be used directly after a satisfiability check returned SAT.");
    checkState(
        proverState.lastQueryWasSAT(),
        "The last query was not satisfiable. The called method may only be used directly after a"
            + " satisfiability check returned SAT.");
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(generateModels, TEMPLATE, ProverOptions.GENERATE_MODELS);
    checkNotClosed();
    checkUnchangedSinceLastQuerySatisfiable();
  }

  protected final void checkGenerateAllSat() {
    // TODO: should this close all evaluators as well?
    checkNotClosed();
    Preconditions.checkState(generateAllSat, TEMPLATE, ProverOptions.GENERATE_ALL_SAT);
  }

  protected final void checkGenerateUnsatCores() {
    // TODO: should this close all evaluators as well?
    Preconditions.checkState(generateUnsatCores, TEMPLATE, ProverOptions.GENERATE_UNSAT_CORE);
    checkNotClosed();
    checkUnchangedSinceLastQueryUnsatisfiable();
  }

  protected final void checkIsUnsatOverAssumptions(Collection<BooleanFormula> assumptions) {
    checkNotClosed();
    Preconditions.checkNotNull(assumptions);
  }

  protected final void checkGenerateUnsatCoresOverAssumptions(
      Collection<BooleanFormula> assumptions) {
    // TODO: should this close all evaluators as well?
    // No need to no check for changedSinceLastSatQuery or wasLastSatCheckSatisfiable, as we
    // guarantee a call to isUnsatOverAssumptions()
    checkIsUnsatOverAssumptions(assumptions);
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        TEMPLATE,
        ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
  }

  private void checkGenerateInterpolants() {
    // TODO: should this close all evaluators as well?
    checkNotClosed();
    checkUnchangedSinceLastQueryUnsatisfiable();
  }

  protected final void checkGenerateInterpolants(Collection<T> formulasOfA) {
    checkGenerateInterpolants();
    checkArgument(
        getAssertedConstraintIds().containsAll(formulasOfA),
        "interpolation can only be done over previously asserted formulas.");
  }

  protected final void checkGenerateSeqInterpolants(
      List<? extends Collection<T>> partitionedFormulas) {
    checkGenerateInterpolants();
    Preconditions.checkArgument(
        !partitionedFormulas.isEmpty(), "at least one partition should be available.");
    final ImmutableSet<T> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        partitionedFormulas.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");
  }

  protected final void checkGenerateTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree) {
    checkGenerateSeqInterpolants(partitionedFormulas);
    assert InterpolatingProverEnvironment.checkTreeStructure(
        partitionedFormulas.size(), startOfSubTree);
  }

  protected final void checkEnableSeparationLogic() {
    checkNotClosed();
    Preconditions.checkState(enableSL, TEMPLATE, ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  protected abstract boolean hasPersistentModel();

  /**
   * Sets the flags such that the prover state was changed since the last SAT check and closes all
   * evaluators.
   */
  private void setProverStateToChangedSinceLastQuery() {
    if (proverState != ProverState.CHANGED_SINCE_LAST_SAT_QUERY) {
      proverState = ProverState.CHANGED_SINCE_LAST_SAT_QUERY;
      if (!hasPersistentModel()) {
        closeAllEvaluators();
      }
    }
  }

  /**
   * Modifies the current solver state to unchanged since last satisfiability check and remembers
   * its result. Example usage:
   *
   * <p>{@code boolean isUnsat = setProverStateByIsUnsat(isUnsatImpl())}
   *
   * @param isUnsat the result of {@link #isUnsat()} (and similar methods) that guarantee returning
   *     {@code true} for UNSAT and {@code false} for SAT.
   * @return the unchanged parameter 'isUnsat'.
   */
  @CanIgnoreReturnValue
  protected boolean setProverStateByIsUnsat(final boolean isUnsat) {
    if (isUnsat) {
      proverState = ProverState.UNCHANGED_UNSAT;
    } else {
      proverState = ProverState.UNCHANGED_SAT;
    }
    return isUnsat;
  }

  /**
   * Modifies the current solver state to unchanged since last satisfiability check and remembers
   * its result. The prover state is set to {@link ProverState#UNCHANGED_SAT} only for {@link
   * OptStatus#OPT}, and to {@link ProverState#UNCHANGED_UNSAT} in all other cases. Example usage:
   *
   * <p>{@code OptStatus optStatus = setProverStateByOptStatus(checkImpl(query))}
   *
   * @param optimizationStatus the result of {@link #check()} (and similar methods) that return
   *     {@link OptStatus}.
   * @return the unchanged parameter 'optimizationStatus'.
   */
  private OptStatus setProverStateByOptStatus(final OptStatus optimizationStatus) {
    if (optimizationStatus == OptStatus.OPT) {
      proverState = ProverState.UNCHANGED_SAT;
    } else {
      proverState = ProverState.UNCHANGED_UNSAT;
    }
    return optimizationStatus;
  }

  @Override
  public int size() {
    checkNotClosed();
    return assertedFormulas.size() - 1;
  }

  @Override
  public final void push() throws InterruptedException {
    checkNotClosed();
    pushImpl();
    setProverStateToChangedSinceLastQuery();
    assertedFormulas.add(LinkedHashMultimap.create());
  }

  protected abstract void pushImpl() throws InterruptedException;

  @Override
  public final void pop() {
    checkNotClosed();
    checkState(assertedFormulas.size() > 1, "initial level must remain until close");
    assertedFormulas.remove(assertedFormulas.size() - 1); // remove last
    popImpl();
    setProverStateToChangedSinceLastQuery();
  }

  protected abstract void popImpl();

  @Override
  @CanIgnoreReturnValue
  public final @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    checkNotClosed();
    T t = addConstraintImpl(constraint);
    setProverStateToChangedSinceLastQuery();
    Iterables.getLast(assertedFormulas).put(constraint, t);
    return t;
  }

  protected abstract @Nullable T addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException;

  /** Check whether the conjunction of all formulas on the stack is unsatisfiable. */
  @Override
  public final boolean isUnsat() throws SolverException, InterruptedException {
    checkNotClosed();
    setProverStateToChangedSinceLastQuery();
    return setProverStateByIsUnsat(isUnsatImpl());
  }

  protected abstract boolean isUnsatImpl() throws SolverException, InterruptedException;

  /**
   * Performs an optimization-aware check and returns the optimization status.
   *
   * <p>This method is the public entry point for optimization checks. It validates that the prover
   * is open, resets internal change-tracking state, and delegates solver-specific work to {@link
   * #checkImpl()}. Subclasses that implement optimization support must provide the actual checking
   * logic in {@code checkImpl()}.
   *
   * <p>The signature of this method matches that of {@link OptimizationProverEnvironment#check()},
   * to allow overrides in subclasses that implement both {@link BasicProverEnvironment} and {@link
   * OptimizationProverEnvironment}.
   *
   * @return the optimization status; {@link OptStatus#OPT} indicates a satisfiable/optimal result
   */
  public final OptStatus check() throws InterruptedException, SolverException {
    checkNotClosed();
    setProverStateToChangedSinceLastQuery();
    return setProverStateByOptStatus(checkImpl());
  }

  /**
   * Implementation of optimization-aware satisfiability-check.
   *
   * @throws InterruptedException if the thread is interrupted during the check
   * @throws SolverException if the underlying solver reports an error
   * @throws UnsupportedOperationException if optimization is not supported by this prover
   */
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
   * Flatten and inverse the prover-stack and return all asserted constraints.
   *
   * <p>Each formula can be asserted several times. However, each assertion has a unique id. This
   * implies that the inverted mapping is a plain {@link Map}, not a {@link Multimap}.
   */
  protected ImmutableMap<T, BooleanFormula> getAssertedFormulasById() {
    ImmutableMap.Builder<T, BooleanFormula> builder = ImmutableMap.builder();
    for (Multimap<BooleanFormula, T> level : assertedFormulas) {
      for (Entry<BooleanFormula, T> entry : level.entries()) {
        // the id (entry.value) is unique across all levels.
        builder.put(entry.getValue(), entry.getKey());
      }
    }
    return builder.buildOrThrow();
  }

  @Override
  public final Model getModel() throws SolverException {
    checkGenerateModels();
    return getModelImpl();
  }

  protected abstract Model getModelImpl() throws SolverException;

  @Override
  public final Evaluator getEvaluator() throws SolverException {
    checkGenerateModels();
    return getEvaluatorImpl();
  }

  protected Evaluator getEvaluatorImpl() throws SolverException {
    return getModel();
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

  // Note: this is also overridden and implemented in our assumptions wrapper (i.e.
  // BasicProverWithAssumptionsWrapper and its children), without checks/flags. But the
  // implementation in the assumptions wrapper is guaranteed to use other methods that are
  // checked and set the flags correctly (push() and isUnsat()), so we can safely ignore it.
  @Override
  public final boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    checkIsUnsatOverAssumptions(assumptions);
    setProverStateToChangedSinceLastQuery();
    return setProverStateByIsUnsat(isUnsatWithAssumptionsImpl(assumptions));
  }

  /**
   * @implNote implementing this assumes that {@link
   *     AbstractSolverContext#supportsAssumptionSolving()} is also overridden returning {@code
   *     true} in the {@link org.sosy_lab.java_smt.api.SolverContext} implementation of this solver,
   *     as otherwise this method is ignored.
   */
  protected abstract boolean isUnsatWithAssumptionsImpl(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException;

  @Override
  public final List<BooleanFormula> getUnsatCore() {
    checkGenerateUnsatCores();
    return getUnsatCoreImpl();
  }

  /**
   * @implSpec override and implement if a solver supports UNSAT-CORE generation.
   */
  protected List<BooleanFormula> getUnsatCoreImpl() {
    throw new UnsupportedOperationException(UNSAT_CORE_NOT_SUPPORTED);
  }

  @Override
  public final Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    checkGenerateUnsatCoresOverAssumptions(assumptions);
    setProverStateToChangedSinceLastQuery();
    // Since some unsatCoreOverAssumptionsImpl() implementations don't use isUnsatWithAssumptions(),
    // we can not give any guarantees (set flags) after calling unsatCoreOverAssumptionsImpl().
    // Flags need to be set by the implementation correctly.
    return unsatCoreOverAssumptionsImpl(assumptions);
  }

  /**
   * @implSpec override and implement if a solver supports the generation of UNSAT-COREs over
   *     assumptions. This implementation must guarantee that {@link
   *     BasicProverEnvironment#isUnsatWithAssumptions(Collection)}, or equivalent code that
   *     establishes satisfiability is called before generating the unsat-core. The prover state
   *     needs to be set correctly after the satisfiability check (e.g. {@link
   *     #setProverStateByIsUnsat(boolean)} if you can guarantee that the result is usable after
   *     returning from this method). You can expect that the prover state is set the {@link
   *     ProverState#CHANGED_SINCE_LAST_SAT_QUERY} before this method is called. Else, override and
   *     throw a {@link UnsupportedOperationException} with {@link
   *     BasicProverEnvironment#UNSAT_CORE_WITH_ASSUMPTIONS_NOT_SUPPORTED}.
   */
  protected abstract Optional<List<BooleanFormula>> unsatCoreOverAssumptionsImpl(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException;

  @Override
  public final <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    checkGenerateAllSat();
    return allSatImpl(callback, important);
  }

  /**
   * @implSpec only override and implement if a solver offers its own AllSAT procedure, otherwise
   *     inherit {@link AbstractProverWithAllSat} instead of this class.
   */
  protected abstract <R> R allSatImpl(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException;

  @Override
  public final ImmutableMap<String, String> getStatistics() {
    checkNotClosed();
    return getStatisticsImpl();
  }

  /**
   * @implSpec override and implement for solvers that provide statistics.
   */
  protected ImmutableMap<String, String> getStatisticsImpl() {
    return ImmutableMap.of();
  }

  @Override
  public void close() {
    assertedFormulas.clear();
    closeAllEvaluators();
    proverState = ProverState.CLOSED;
  }
}
