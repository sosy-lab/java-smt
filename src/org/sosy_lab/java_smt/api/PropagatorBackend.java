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

import java.util.Optional;

/**
 * The PropagatorBackend class is used by {@link UserPropagator} to implement custom user
 * propagators.
 * It contains functions to interact with the SAT/SMT core during solving, for example, it provides
 * the ability to propagate conflicts.
 */
public interface PropagatorBackend {

  /**
   * Registers an expression to be observed by a {@link UserPropagator}.
   * Whenever the value of a registered expression becomes known by the solver, this will
   * get reported to the user propagator by invoking the callback
   * {@link UserPropagator#onKnownValue} (if notification was enabled via
   * {@link #notifyOnKnownValue}).
   *
   * @param theoryExpr The expression to observe.
   */
  void registerExpression(BooleanFormula theoryExpr);

  /**
   * Raises a conflict caused by a set of conflicting assignments. Shall only be called
   * from within a callback by {@link UserPropagator} such as
   * {@link UserPropagator#onKnownValue} and
   * {@link UserPropagator#onFinalCheck()}.
   *
   * <p> Effectively causes the solver to learn the implication "{@code conflictExpressions} =>
   *   false"
   *
   * @param conflictExpressions A set of inconsistent assignments.
   */
  void propagateConflict(BooleanFormula[] conflictExpressions);

  /**
   * Propagates a consequence implied by a set of assigned expressions. Shall only be called
   * from within a callback by {@link UserPropagator} such as
   * {@link UserPropagator#onKnownValue} and
   * {@link UserPropagator#onFinalCheck()}.
   *
   * <p> Effectively causes the solver to learn the implication "/\ {@code assignedExpressions} =>
   * {@code consequence}"
   * It is possible to have an empty set of {@code assignedExpressions} to generate a theory lemma.
   *
   * @param assignedExpressions A set of assigned expressions.
   * @param consequence      The consequence implied by the assigned expressions.
   */
  void propagateConsequence(BooleanFormula[] assignedExpressions, BooleanFormula consequence);

  /**
   * Propagates a decision to be made by the solver.
   * If called during {@link UserPropagator#onKnownValue}, will set the next decision to be made.
   *
   * @param expr The expression to assign to next.
   * @param value   The value to be assigned. If not given, the solver will decide.
   * @return False, if the value of {@code expr} is already assigned. True, otherwise.
   * Note that the value of {@code expr} may already be decided before being reported via
   * {@link UserPropagator#onKnownValue}.
   */
  boolean propagateNextDecision(BooleanFormula expr, Optional<Boolean> value);

  /**
   * Enables tracking of expression values for the associated {@link UserPropagator} via
   * {@link UserPropagator#onKnownValue(BooleanFormula, BooleanFormula)}.
   *
   * <p>This function is typically called from {@link UserPropagator#initialize()} if the
   * theory solver needs to listen to the value of expressions registered by
   * {@link #registerExpression}.
   */
  void notifyOnKnownValue();

  /**
   * Enables the final callback {@link UserPropagator#onFinalCheck()} that is invoked
   * when the solver finds a full satisfying assignment.
   *
   * <p>This function is typically called from {@link UserPropagator#initialize()} if the
   * theory solver needs to perform final consistency checks.
   */
  void notifyOnFinalCheck();
}
