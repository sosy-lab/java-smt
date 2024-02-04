// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

/**
 * Allows user-defined propagators (~ theory solvers) to be implemented.
 * It is advised to inherit from {@link org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator}
 * rather than implementing this interface directly.
 *
 * <p> A user propagator provides various callbacks that are invoked by the solver during the
 * solving process. Within these callbacks, the user can react to and influence the solver
 * by calling into the {@link PropagatorBackend}. For example, he can raise conflicts
 * whenever the solver makes assignments inconsistent to the user-defined theory.
 */
public interface UserPropagator {

  /**
   * This callback is invoked whenever the solver creates a new decision level.
   * A user propagator should maintain backtracking points on each push to enable later
   * backtracking.
   */
  void onPush();

  /**
   * This callback is invoked when the solver backtracks. The solver can backtrack multiple
   * levels simultaneously.
   * @param numPoppedLevels The number of levels to backtrack (~ number of pushes to backtrack).
   */
  void onPop(int numPoppedLevels);

  /**
   * This callback is invoked when the solver finds a complete satisfying assignment.
   * The user can check the found model for consistency and potentially raise conflicts via
   * {@link PropagatorBackend#propagateConflict(BooleanFormula[])}.
   * <p>
   * Note: This callback is only invoked if the user propagator enabled it via
   * {@link PropagatorBackend#notifyOnFinalCheck()}.
   */
  void onFinalCheck();

  /**
   * This callback is invoked if the solver gets to know the value of a registered expression
   * ({@link #registerExpression}).
   * Within the callback, the user can raise conflicts via
   * {@link PropagatorBackend#propagateConflict}, propagate consequences via
   * {@link PropagatorBackend#propagateConsequence}, or influence the solvers decision heuristics
   * via {@link PropagatorBackend#propagateNextDecision}.
   * <p>
   * The reported value is only known on the current and later push levels,
   * but will get invalidated when backtracking.
   * <p>
   * Note: This callback is only invoked if the user propagator enabled it via
   * {@link PropagatorBackend#notifyOnKnownValue()}.
   *
   * @param expr  The expressions whose value is known.
   * @param value The value of the expression (true or false).
   */
  void onKnownValue(BooleanFormula expr, BooleanFormula value);

  /**
   * This callback is invoked if the solver decides to branch on a registered expression.
   * ({@link #registerExpression}).
   * Within the callback, the user can change the decision by calling
   * {@link PropagatorBackend#propagateNextDecision}.
   * <p>
   * Note: This callback is only invoked if the user propagator enabled it via
   * {@link PropagatorBackend#notifyOnDecision()}.
   * @param expr The expressions whose value gets decided (usually a literal).
   * @param value The decision value.
   */
  void onDecision(BooleanFormula expr, boolean value);

  /**
   * Connects this user propagator with a {@link PropagatorBackend}. The backend is used
   * to register expressions, raise conflicts, propagate consequences, etc.
   * @param backend The propagator backend.
   */
  void injectBackend(PropagatorBackend backend);

  /**
   * This method is similar to a constructor but is guaranteed to get invoked only after
   * {@link #injectBackend} was successfully called.
   * The user can enable notifications by accessing the injected {@link PropagatorBackend}.
   */
  void initialize();

  /**
   * Registers an expression to be observed by the {@link UserPropagator}.
   * Solver actions related to the expression are reported:
   * <ul>
   *   <li>
   *     The callback {@link UserPropagator#onKnownValue} gets invoked if the value of a
   *     registered expression becomes known (if notification was enabled via
   *    {@link PropagatorBackend#notifyOnKnownValue}).
   *   </li>
   *   <li>
   *     The callback {@link UserPropagator#onDecision} gets invoked right before the
   *     solver decides on the value of a registered expression (if notification was enabled via
   *     {@link PropagatorBackend#notifyOnDecision()}).
   *   </li>
   * </ul>
   *
   * @param theoryExpr The expression to observe.
   */
  void registerExpression(BooleanFormula theoryExpr);


}
