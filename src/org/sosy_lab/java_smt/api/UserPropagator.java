/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

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
   *
   * Note: This callback is only invoked if the user propagator enabled it via
   * {@link PropagatorBackend#notifyOnFinalCheck()}.
   */
  void onFinalCheck();

  /**
   * This callback is invoked if the solver finds two registered expressions
   * ({@link #registerExpression})
   * to be equal.
   *
   * <p>The solver may not report all quadratically-many equalities. Instead, the solver may report
   * only linearly many equalities (~ a spanning tree) that are sufficient to reconstruct the full
   * equivalence relation (e.g., via a union-find data structure).
   *
   * <p>The reported equalities hold only true on the current and later push levels,
   * but will in general get invalidated when backtracking.
   *
   * Note: This callback is only invoked if the user propagator enabled it via
   * {@link PropagatorBackend#notifyOnEquality()}.
   * @param x The first expression.
   * @param y The second expression that equals the first one.
   */
  void onEquality(BooleanFormula x, BooleanFormula y);

  /**
   * This callback is invoked if the solver gets to know the value of a registered expression
   * ({@link #registerExpression}).
   *
   * Note: This callback is only invoked if the user propagator enabled it via
   * {@link PropagatorBackend#notifyOnKnownValue()}.
   * @param expr The expressions whose value is known.
   * @param val The value of the expression (true or false).
   */
  void onKnownValue(BooleanFormula expr, BooleanFormula val);

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
   * Whenever the value of a registered expression becomes known by the solver, this will
   * get reported to the user propagator by invoking the callback
   * {@link UserPropagator#onKnownValue} (if notification was enabled via
   * {@link PropagatorBackend#notifyOnKnownValue}).
   * Similarly, equalities between registered expressions are reported via
   * {@link UserPropagator#onEquality} (if enabled via
   * {@link PropagatorBackend#notifyOnEquality()}.
   * @param theoryExpr The expression to observe.
   */
  void registerExpression(BooleanFormula theoryExpr);


}
