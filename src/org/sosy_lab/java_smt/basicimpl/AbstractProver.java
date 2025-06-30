// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.MoreStrings;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  private final boolean generateModels;
  private final boolean generateAllSat;
  protected final boolean generateUnsatCores;
  private final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;
  protected boolean closed = false;
  protected boolean wasLastSatCheckSat = false;
  protected boolean stackChangedSinceLastQuery = false;

  private final Set<Evaluator> evaluators = new LinkedHashSet<>();

  /**
   * This data-structure tracks all formulas that were asserted on different levels. We can assert a
   * formula multiple times on the same or also distinct levels and return a new ID for each
   * assertion.
   */
  private final List<Multimap<BooleanFormula, T>> assertedFormulas = new ArrayList<>();

  private static final String TEMPLATE = "Please set the prover option %s.";

  protected final @Nullable ShutdownNotifier proverShutdownNotifier;
  protected final ShutdownNotifier contextShutdownNotifier;

  protected AbstractProver(
      ShutdownNotifier pContextShutdownNotifier,
      @Nullable ShutdownNotifier pProverShutdownNotifier,
      Set<ProverOptions> pOptions) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateAllSat = pOptions.contains(ProverOptions.GENERATE_ALL_SAT);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    enableSL = pOptions.contains(ProverOptions.ENABLE_SEPARATION_LOGIC);

    assertedFormulas.add(LinkedHashMultimap.create());

    contextShutdownNotifier = pContextShutdownNotifier;
    proverShutdownNotifier = pProverShutdownNotifier;
  }

  protected final void shutdownIfNecessary() throws InterruptedException {
    contextShutdownNotifier.shutdownIfNecessary();
    if (proverShutdownNotifier != null) {
      proverShutdownNotifier.shutdownIfNecessary();
    }
  }

  protected final boolean shouldShutdown() {
    if (proverShutdownNotifier != null) {
      return contextShutdownNotifier.shouldShutdown() || proverShutdownNotifier.shouldShutdown();
    }
    return contextShutdownNotifier.shouldShutdown();
  }

  public void checkShutdownState() {
    if (shouldShutdown()) {
      throw new IllegalStateException(getShutdownReason());
    }
  }

  /**
   * Only to be called when at least one of the shutdown notifiers is supposed to be shutting down!
   * Throws an Exception if no shutdown is requested!
   */
  protected final String getShutdownReason() {
    if (proverShutdownNotifier != null && proverShutdownNotifier.shouldShutdown()) {
      return SHUTDOWN_EXCEPTION_PREFIX + proverShutdownNotifier.getReason();
    }

    return SHUTDOWN_EXCEPTION_PREFIX + contextShutdownNotifier.getReason();
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(generateModels, TEMPLATE, ProverOptions.GENERATE_MODELS);
  }

  protected final void checkGenerateAllSat() {
    Preconditions.checkState(generateAllSat, TEMPLATE, ProverOptions.GENERATE_ALL_SAT);
  }

  private void checkGenerateUnsatCores() {
    Preconditions.checkState(generateUnsatCores, TEMPLATE, ProverOptions.GENERATE_UNSAT_CORE);
  }

  private void checkGenerateUnsatCoresOverAssumptions() {
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        TEMPLATE,
        ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
  }

  protected final void checkEnableSeparationLogic() {
    Preconditions.checkState(enableSL, TEMPLATE, ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Override
  public int size() {
    checkState(!closed);
    return assertedFormulas.size() - 1;
  }

  @Override
  public final boolean isUnsat() throws SolverException, InterruptedException {
    checkState(!closed);
    closeAllEvaluators();
    shutdownIfNecessary();
    wasLastSatCheckSat = !isUnsatImpl();
    stackChangedSinceLastQuery = false;
    return !wasLastSatCheckSat;
  }

  protected abstract boolean isUnsatImpl() throws SolverException, InterruptedException;

  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkState(!closed);
    checkShutdownState();
    checkState(!wasLastSatCheckSat, NO_UNSAT_CORE_HELP);
    checkState(!stackChangedSinceLastQuery, STACK_CHANGED_HELP);
    checkGenerateUnsatCores();
    return getUnsatCoreImpl();
  }

  protected abstract List<BooleanFormula> getUnsatCoreImpl();

  @Override
  public final Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    checkState(!closed);
    shutdownIfNecessary();
    checkGenerateUnsatCoresOverAssumptions();
    return unsatCoreOverAssumptionsImpl(assumptions);
  }

  protected abstract Optional<List<BooleanFormula>> unsatCoreOverAssumptionsImpl(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException;

  @Override
  public final boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    checkState(!closed);
    shutdownIfNecessary();
    stackChangedSinceLastQuery = false;
    return isUnsatWithAssumptionsImpl(assumptions);
  }

  protected abstract boolean isUnsatWithAssumptionsImpl(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException;

  @Override
  public final Model getModel() throws SolverException {
    checkState(!closed);
    checkShutdownState();
    checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkState(!stackChangedSinceLastQuery, STACK_CHANGED_HELP);
    checkGenerateModels();
    return getModelImpl();
  }

  protected abstract Model getModelImpl() throws SolverException;

  @Override
  public final Evaluator getEvaluator() throws SolverException {
    checkState(!closed);
    checkShutdownState();
    checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkState(!stackChangedSinceLastQuery, STACK_CHANGED_HELP);
    checkGenerateModels();
    return getEvaluatorImpl();
  }

  protected Evaluator getEvaluatorImpl() throws SolverException {
    return getModel();
  }

  @Override
  public final void push() throws InterruptedException {
    checkState(!closed);
    shutdownIfNecessary();
    pushImpl();
    stackChangedSinceLastQuery = true;
    assertedFormulas.add(LinkedHashMultimap.create());
  }

  protected abstract void pushImpl() throws InterruptedException;

  @Override
  public final void pop() {
    checkState(!closed);
    checkShutdownState();
    checkState(assertedFormulas.size() > 1, "initial level must remain until close");
    assertedFormulas.remove(assertedFormulas.size() - 1); // remove last
    // TODO: technically only needed if the level removed was non empty.
    stackChangedSinceLastQuery = true;
    wasLastSatCheckSat = false;
    popImpl();
  }

  protected abstract void popImpl();

  @Override
  @CanIgnoreReturnValue
  public final @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    checkState(!closed);
    shutdownIfNecessary();
    T t = addConstraintImpl(constraint);
    Iterables.getLast(assertedFormulas).put(constraint, t);
    stackChangedSinceLastQuery = true;
    wasLastSatCheckSat = false;
    return t;
  }

  protected abstract @Nullable T addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException;

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

  protected void checkInterpolationArguments(Collection<T> formulasOfA) {
    checkArgument(
        getAssertedConstraintIds().containsAll(formulasOfA),
        "Interpolation can only be done over previously asserted formulas. %s",
        MoreStrings.lazyString(() -> getErrorString(formulasOfA)).toString());
  }

  private String getErrorString(Collection<T> formulasOfA) {
    ImmutableSet.Builder<T> builder = ImmutableSet.builder();
    for (T formula : formulasOfA) {
      if (formula == null) {
        return "Null element found, but not allowed.";
      } else {
        builder.add(formula);
      }
    }
    return "Missing IDs: " + builder.build();
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
  public ImmutableList<Model.ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    checkShutdownState();
    Preconditions.checkState(!stackChangedSinceLastQuery, STACK_CHANGED_HELP);
    checkState(wasLastSatCheckSat);
    try (Model model = getModel()) {
      return model.asList();
    }
  }

  @Override
  public void close() {
    assertedFormulas.clear();
    closeAllEvaluators();
    closed = true;
  }
}
