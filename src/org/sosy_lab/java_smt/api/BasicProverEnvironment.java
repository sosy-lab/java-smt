// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

/**
 * Super interface for {@link ProverEnvironment} and {@link InterpolatingProverEnvironment} that
 * provides only the common operations. In most cases, just use one of the two sub-interfaces
 */
public interface BasicProverEnvironment<T> extends AutoCloseable {

  /**
   * Push a backtracking point and add a formula to the current stack, asserting it. The return
   * value may be used to identify this formula later on in a query (this depends on the subtype of
   * the environment).
   */
  @Nullable
  @CanIgnoreReturnValue
  default T push(BooleanFormula f) throws InterruptedException, SolverException {
    push();
    return addConstraint(f);
  }

  /**
   * Remove one backtracking point/level from the current stack. This removes the latest level
   * including all of its formulas, i.e., all formulas that were added for this backtracking point.
   */
  void pop() throws InterruptedException;

  /** Add a constraint to the latest backtracking point. */
  @Nullable
  @CanIgnoreReturnValue
  T addConstraint(BooleanFormula constraint) throws InterruptedException, SolverException;

  /**
   * Create a new backtracking point, i.e., a new level on the assertion stack. Each level can hold
   * several asserted formulas.
   *
   * <p>If formulas are added before creating the first backtracking point, they can not be removed
   * via a POP-operation.
   */
  void push() throws InterruptedException, SolverException;

  /**
   * Get the number of backtracking points/levels on the current stack.
   *
   * <p>Caution: This is the number of PUSH-operations, and not necessarily equal to the number of
   * asserted formulas. On any level there can be an arbitrary number of asserted formulas. Even
   * with size of 0, formulas can already be asserted (at bottom level).
   */
  int size();

  /** Check whether the conjunction of all formulas on the stack is unsatisfiable. */
  boolean isUnsat() throws SolverException, InterruptedException;

  /**
   * Check whether the conjunction of all formulas on the stack together with the list of
   * assumptions is satisfiable.
   *
   * @param assumptions A list of literals.
   */
  boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException;

  /**
   * Get a satisfying assignment. This method should be called only immediately after an {@link
   * #isUnsat()} call that returned <code>false</code>. The returned model is guaranteed to stay
   * constant and valid as long as the solver context is available, even if constraints are added
   * to, pushed or popped from the prover stack.
   *
   * <p>A model might contain additional symbols with their evaluation, if a solver uses its own
   * temporary symbols. There should be at least a value-assignment for each free symbol.
   */
  Model getModel() throws SolverException, InterruptedException;

  /**
   * Get a temporary view on the current satisfying assignment. This should be called only
   * immediately after an {@link #isUnsat()} call that returned <code>false</code>. The evaluator
   * should no longer be used as soon as any constraints are added to, pushed, or popped from the
   * prover stack.
   */
  default Evaluator getEvaluator() throws SolverException, InterruptedException {
    return getModel();
  }

  /**
   * Get a list of satisfying assignments. This is equivalent to <code>
   * ImmutableList.copyOf(getModel())</code>, but removes the need for calling {@link
   * Model#close()}.
   *
   * <p>Note that if you need to iterate multiple times over the model it may be more efficient to
   * use this method instead of {@link #getModel()} (depending on the solver).
   */
  default ImmutableList<Model.ValueAssignment> getModelAssignments()
      throws SolverException, InterruptedException {
    try (Model model = getModel()) {
      return model.asList();
    }
  }

  /**
   * Get an unsat core. This should be called only immediately after an {@link #isUnsat()} call that
   * returned <code>false</code>.
   */
  List<BooleanFormula> getUnsatCore() throws InterruptedException;

  /**
   * Returns an UNSAT core (if it exists, otherwise {@code Optional.empty()}), over the chosen
   * assumptions. Does NOT require the {@link ProverOptions#GENERATE_UNSAT_CORE} option to work, but
   * {@link ProverOptions#GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS}.
   *
   * @param assumptions Selected assumptions
   * @return Empty optional if the constraints with assumptions are satisfiable, subset of
   *     assumptions which is unsatisfiable with the original constraints otherwise.
   */
  Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException;

  /**
   * Get statistics for a concrete ProverEnvironment in a solver. The returned mapping is intended
   * to provide solver-internal statistics for only this instance. The keys can differ between
   * individual solvers.
   *
   * <p>Calling the statistics several times for the same {@link ProverEnvironment}s returns
   * accumulated number, i.e., we currently do not provide any possibility to reset the statistics.
   * Calling the statistics for different {@link ProverEnvironment}s returns independent statistics.
   *
   * <p>We do not guarantee any specific key to be present, as this depends on the used solver. We
   * might even return an empty mapping if the solver does not support calling this method or is in
   * an invalid state.
   *
   * @see SolverContext#getStatistics()
   */
  default ImmutableMap<String, String> getStatistics() {
    return ImmutableMap.of();
  }

  /**
   * Closes the prover environment. The object should be discarded, and should not be used after
   * closing. The first call of this method will close the prover instance, further calls are
   * ignored.
   */
  @Override
  void close();

  /**
   * Get all satisfying assignments of the current environment with regard to a subset of terms, and
   * create a region representing all those models.
   *
   * @param important A set of (positive) variables appearing in the asserted queries. Only these
   *     variables will appear in the region.
   * @return A region representing all satisfying models of the formula.
   */
  <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException;

  /**
   * Interface for the {@link #allSat} callback.
   *
   * @param <R> The result type of the callback, passed through by {@link #allSat}.
   */
  interface AllSatCallback<R> {

    /**
     * Callback for each possible satisfying assignment to given {@code important} predicates. If
     * the predicate is assigned {@code true} in the model, it is returned as-is in the list, and
     * otherwise it is negated.
     *
     * <p>There is no guarantee that the list of model values corresponds to the list in {@link
     * BasicProverEnvironment#allSat}. We can reorder the variables or leave out values with a
     * freely chosen value.
     */
    void apply(List<BooleanFormula> model);

    /** Returning the result generated after all the {@link #apply} calls went through. */
    R getResult() throws InterruptedException;
  }

  /**
   * Registers a {@link UserPropagator} for this prover environment. Only a single user propagator
   * can be registered at a time, and each user propagator shall only be registered once in its
   * lifetime (see also {@link UserPropagator#initializeWithBackend}).
   *
   * @param propagator The (fresh) user propagator to register.
   * @return {@code true}, if the user propagator was successfully registered. Most SMT solvers do
   *     not support user propagators and hence return {@code false}.
   */
  default boolean registerUserPropagator(UserPropagator propagator) {
    return false;
  }
}
