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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  // flags for option
  protected final boolean generateModels;
  protected final Optional<ProverOptions> generateAllSat;
  protected final boolean generateUnsatCores;
  protected final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;

  // flags for status
  protected boolean closed = false;
  protected boolean wasLastSatCheckSatisfiable = true; // assume SAT for an empty prover
  protected boolean changedSinceLastSatQuery = true; // assume changed for an empty prover

  private final Set<Evaluator> evaluators = new LinkedHashSet<>();

  protected final ShutdownNotifier shutdownNotifier;
  private final BooleanFormulaManager bmgr;

  /**
   * This data-structure tracks all formulas that were asserted on different levels. We can assert a
   * formula multiple times on the same or also distinct levels and return a new ID for each
   * assertion.
   */
  private final List<Multimap<BooleanFormula, T>> assertedFormulas = new ArrayList<>();

  private static final String TEMPLATE = "Please set a prover option including %s.";

  protected AbstractProver(
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateAllSat = getAllSatOption(pOptions);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    enableSL = pOptions.contains(ProverOptions.ENABLE_SEPARATION_LOGIC);

    assertedFormulas.add(LinkedHashMultimap.create());

    bmgr = pBmgr;
    shutdownNotifier = pShutdownNotifier;
  }

  private Optional<ProverOptions> getAllSatOption(Set<ProverOptions> pOptions) {
    Optional<ProverOptions> allSatOp = Optional.empty();
    for (ProverOptions op : pOptions) {
      if (ImmutableSet.of(
              ProverOptions.GENERATE_ALL_SAT,
              ProverOptions.GENERATE_ALL_SAT_NATIVE,
              ProverOptions.GENERATE_ALL_SAT_MODEL_BASED,
              ProverOptions.GENERATE_ALL_SAT_MODEL_BASED_W_FALLBACK,
              ProverOptions.GENERATE_ALL_SAT_PREDICATE_COMBINATIONS,
              ProverOptions.GENERATE_ALL_SAT_PREDICATE_COMBINATIONS_W_FALLBACK)
          .contains(op)) {
        if (allSatOp.isEmpty()) {
          allSatOp = Optional.of(op);
        } else {
          throw new IllegalArgumentException(
              "Only a single AllSAT ProverOption is allowed. Found"
                  + " "
                  + op
                  + " and "
                  + allSatOp.orElseThrow());
        }
      }
    }
    return allSatOp;
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(generateModels, TEMPLATE, ProverOptions.GENERATE_MODELS);
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    Preconditions.checkState(wasLastSatCheckSatisfiable, NO_MODEL_HELP);
  }

  protected final void checkGenerateAllSat() {
    // TODO: should this close all evaluators as well?
    Preconditions.checkState(!closed);
    Preconditions.checkState(generateAllSat.isPresent(), TEMPLATE, ProverOptions.GENERATE_ALL_SAT);
  }

  protected final void checkGenerateUnsatCores() {
    // TODO: should this close all evaluators as well?
    Preconditions.checkState(generateUnsatCores, TEMPLATE, ProverOptions.GENERATE_UNSAT_CORE);
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    Preconditions.checkState(!wasLastSatCheckSatisfiable);
  }

  protected final void checkGenerateUnsatCoresOverAssumptions(
      Collection<BooleanFormula> assumptions) {
    // TODO: should this close all evaluators as well?
    Preconditions.checkState(!closed);
    Preconditions.checkNotNull(assumptions);
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        TEMPLATE,
        ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    // TODO: why is there no check for changedSinceLastSatQuery or wasLastSatCheckSatisfiable?
  }

  /**
   * Checks whether the prover has been closed already. Only to be used if this is the only check
   * performed in a call.
   */
  protected void checkClosed() {
    Preconditions.checkState(!closed);
  }

  private void checkGenerateInterpolants() {
    // TODO: should this close all evaluators as well?
    Preconditions.checkState(!closed);
    Preconditions.checkState(
        !changedSinceLastSatQuery,
        "Interpolants can only be calculated right after a call to isUnsat()");
    Preconditions.checkState(
        !wasLastSatCheckSatisfiable,
        "Interpolants can only be calculated if the assertions on the solver stack are "
            + "unsatisfiable.");
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
  @Override
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
    checkState(!closed);
    wasLastSatCheckSatisfiable = false;
    changedSinceLastSatQuery = false;
    final OptStatus status = checkImpl();
    if (status == OptStatus.OPT) {
      wasLastSatCheckSatisfiable = true;
    }
    return status;
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
  public final Model getModel() throws SolverException, InterruptedException {
    checkGenerateModels();
    shutdownNotifier.shutdownIfNecessary();
    return getModelImpl();
  }

  protected abstract Model getModelImpl() throws SolverException;

  @Override
  public final Evaluator getEvaluator() throws SolverException, InterruptedException {
    checkGenerateModels();
    return getEvaluatorImpl();
  }

  protected Evaluator getEvaluatorImpl() throws SolverException, InterruptedException {
    shutdownNotifier.shutdownIfNecessary();
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
    return unsatCoreOverAssumptionsImpl(assumptions);
  }

  /**
   * TODO: once javac does not complain if we use a default impl here, add one.
   *
   * @implSpec override and implement if a solver supports the generation of UNSAT-COREs over
   *     assumptions. Else, override and throw a {@link UnsupportedOperationException} with {@link
   *     BasicProverEnvironment#UNSAT_CORE_WITH_ASSUMPTIONS_NOT_SUPPORTED}
   */
  protected abstract Optional<List<BooleanFormula>> unsatCoreOverAssumptionsImpl(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException;

  @Override
  public final <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    checkGenerateAllSat();

    ProverOptions allSatOp = generateAllSat.orElseThrow();
    if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_NATIVE)) {
      return allSatImpl(callback, important);
    } else if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT)) {
      try {
        return allSatImpl(callback, important);
      } catch (UnsupportedOperationException e) {
        // Fallthrough to independent AllSAT
      }
    }

    return independentAllSatImpl(callback, important);
  }

  /**
   * @implSpec override and implement if a solver offers its own AllSAT procedure. In cases in which
   *     solvers need special handling, e.g. for exceptions, this must call independentAllSatImpl().
   *     Otherwise, throw a {@link UnsupportedOperationException}.
   */
  protected abstract <R> R allSatImpl(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException;

  @Override
  public void close() {
    assertedFormulas.clear();
    closeAllEvaluators();
    closed = true;
  }

  protected <R> R independentAllSatImpl(
      AllSatCallback<R> callback, List<BooleanFormula> importantPredicates)
      throws InterruptedException, SolverException {
    ProverOptions allSatOp = generateAllSat.orElseThrow();
    push();
    if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_NATIVE)) {
      // Needed due to Z3
      throw new UnsupportedOperationException("Solver does not support native AllSAT computation");
    } else if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT)
        || allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_MODEL_BASED_W_FALLBACK)
        || allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_MODEL_BASED)) {
      try {
        // try model-based computation of ALLSAT
        iterateOverAllModels(callback, importantPredicates);
      } catch (SolverException e) {
        if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_MODEL_BASED)) {
          throw e;
        }
        // fallback to direct SAT/UNSAT-based computation of ALLSAT
        iterateOverAllPredicateCombinations(callback, importantPredicates, new ArrayDeque<>());
        // TODO should we completely switch to the second method?
      }
    } else if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_PREDICATE_COMBINATIONS)
        || allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_PREDICATE_COMBINATIONS_W_FALLBACK)) {
      try {
        // fallback to direct SAT/UNSAT-based computation of ALLSAT
        iterateOverAllPredicateCombinations(callback, importantPredicates, new ArrayDeque<>());
      } catch (SolverException e) {
        if (allSatOp.equals(ProverOptions.GENERATE_ALL_SAT_PREDICATE_COMBINATIONS)) {
          throw e;
        }
        // try model-based computation of ALLSAT
        iterateOverAllModels(callback, importantPredicates);
      }
    } else {
      throw new IllegalStateException("Should not be reachable. Reached with option " + allSatOp);
    }
    pop();
    return callback.getResult();
  }

  /**
   * This method computes all satisfiable assignments for the given predicates by iterating over all
   * models. The SMT solver can choose the ordering of variables and shortcut model generation.
   */
  private <R> void iterateOverAllModels(
      AllSatCallback<R> callback, List<BooleanFormula> importantPredicates)
      throws SolverException, InterruptedException {
    final Set<ImmutableList<BooleanFormula>> modelEvaluations = new LinkedHashSet<>();
    while (!isUnsat()) {
      shutdownNotifier.shutdownIfNecessary();

      ImmutableList.Builder<BooleanFormula> valuesOfModel = ImmutableList.builder();
      try (Evaluator evaluator = getEvaluatorWithoutChecks()) {
        for (BooleanFormula formula : importantPredicates) {
          Boolean value = evaluator.evaluate(formula);
          if (value == null) {
            // This is a legal return value for evaluation.
            // The value doesn't matter. We ignore this assignment.
            // This step aim for shortcutting the ALLSAT-loop.
          } else if (value) {
            valuesOfModel.add(formula);
          } else {
            valuesOfModel.add(bmgr.not(formula));
          }
        }
      }

      final ImmutableList<BooleanFormula> values = valuesOfModel.build();
      // avoid endless loops in case of repeated models.
      Preconditions.checkState(
          modelEvaluations.add(values),
          "The model evaluation %s was found before. ALLSAT computation did not make progress.",
          values);
      callback.apply(values);
      shutdownNotifier.shutdownIfNecessary();

      BooleanFormula negatedModel = bmgr.not(bmgr.and(values));
      addConstraint(negatedModel);
      shutdownNotifier.shutdownIfNecessary();
    }
  }

  /**
   * This method computes all satisfiable assignments for the given predicates by (recursively)
   * traversing the decision tree over the given variables. The ordering of variables is fixed, and
   * we can only ignore unsatisfiable subtrees.
   *
   * <p>In contrast to {@link #iterateOverAllModels} we do not use model generation here, which is a
   * benefit for some solvers or theory combinations.
   *
   * @param predicates remaining predicates in the decision tree.
   * @param valuesOfModel already chosen predicate values, ordered as appearing in the tree.
   */
  private <R> void iterateOverAllPredicateCombinations(
      AllSatCallback<R> callback,
      List<BooleanFormula> predicates,
      Deque<BooleanFormula> valuesOfModel)
      throws SolverException, InterruptedException {

    shutdownNotifier.shutdownIfNecessary();

    if (isUnsat()) {
      return;

    } else if (predicates.isEmpty()) {
      // we aim at providing the same order of predicates as given as parameter, thus reverse.
      callback.apply(ImmutableList.copyOf(valuesOfModel).reverse());

    } else {

      // positive predicate
      final BooleanFormula predicate = predicates.get(0);
      valuesOfModel.push(predicate);
      push(predicate);
      iterateOverAllPredicateCombinations(
          callback, predicates.subList(1, predicates.size()), valuesOfModel);
      pop();
      valuesOfModel.pop();

      // negated predicate
      final BooleanFormula notPredicate = bmgr.not(predicates.get(0));
      valuesOfModel.push(notPredicate);
      push(notPredicate);
      iterateOverAllPredicateCombinations(
          callback, predicates.subList(1, predicates.size()), valuesOfModel);
      pop();
      valuesOfModel.pop();
    }
  }

  /**
   * Get an evaluator instance for model evaluation without executing checks for prover options.
   *
   * <p>This method allows model evaluation without explicitly enabling the prover-option {@link
   * ProverOptions#GENERATE_MODELS}. We only use this method internally, when we know about a valid
   * solver state. The returned evaluator does not have caching or any direct optimization for user
   * interaction.
   *
   * @throws SolverException if model can not be constructed.
   */
  protected Evaluator getEvaluatorWithoutChecks() throws SolverException, InterruptedException {
    return getEvaluatorImpl();
  }
}
