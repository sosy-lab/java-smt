// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.util.Optional;

/**
 * The PropagatorBackend class is used by {@link UserPropagator} to implement custom user
 * propagators. It contains functions to interact with the SAT/SMT core during solving, for example,
 * it provides the ability to propagate conflicts and to influence the decision-making.
 */
public interface PropagatorBackend {

  /**
   * Registers an expression to be observed by a {@link UserPropagator}. See {@link
   * UserPropagator#onKnownValue} and {@link UserPropagator#onDecision} for more information.
   *
   * @param theoryExpr The expression to observe.
   */
  void registerExpression(BooleanFormula theoryExpr);

  /**
   * Raises a conflict caused by a set of conflicting assignments. Shall only be called from within
   * a callback by {@link UserPropagator} such as {@link UserPropagator#onKnownValue} and {@link
   * UserPropagator#onFinalCheck()}.
   *
   * <p>Effectively causes the solver to learn the implication "{@code conflictExpressions} =&gt;
   * false"
   *
   * @param conflictExpressions A set of inconsistent assignments.
   */
  void propagateConflict(BooleanFormula[] conflictExpressions);

  /**
   * Propagates a consequence implied by a set of assigned expressions. Shall only be called from
   * within a callback by {@link UserPropagator} such as {@link UserPropagator#onKnownValue} and
   * {@link UserPropagator#onFinalCheck()}.
   *
   * <p>Effectively causes the solver to learn the implication "/\ {@code assignedExpressions} =&gt;
   * {@code consequence}" It is possible to have an empty set of {@code assignedExpressions} to
   * generate a theory lemma.
   *
   * @param assignedExpressions A set of assigned expressions.
   * @param consequence         The consequence implied by the assigned expressions.
   */
  void propagateConsequence(BooleanFormula[] assignedExpressions, BooleanFormula consequence);

  /**
   * Propagates a decision to be made by the solver. If called during {@link
   * UserPropagator#onKnownValue}, will set the next decision to be made. If called during {@link
   * UserPropagator#onDecision}, will overwrite the current decision to be made.
   *
   * @param expr  The expression to assign to next.
   * @param value The value to be assigned. If not given, the solver will decide.
   * @return False, if the value of {@code expr} is already assigned. True, otherwise. Note that the
   * value of {@code expr} may already be decided before being reported via {@link
   * UserPropagator#onKnownValue}.
   */
  boolean propagateNextDecision(BooleanFormula expr, Optional<Boolean> value);

  /**
   * Enables tracking of expression values for the associated {@link UserPropagator} via {@link
   * UserPropagator#onKnownValue}.
   *
   * <p>This function is typically called from {@link UserPropagator#initializeWithBackend} if the
   * theory solver needs to listen to the value of expressions registered by {@link
   * #registerExpression}.
   */
  void notifyOnKnownValue();

  /**
   * Enables tracking of decisions made for the associated {@link UserPropagator} via {@link
   * UserPropagator#onDecision(BooleanFormula, boolean)}.
   *
   * <p>This function is typically called from {@link UserPropagator#initializeWithBackend} if the
   * theory solver needs to listen to and/or modify the decisions made by the solver on expressions
   * registered by {@link #registerExpression}.
   */
  void notifyOnDecision();

  /**
   * Enables the final callback {@link UserPropagator#onFinalCheck()} that is invoked when the
   * solver finds a full satisfying assignment.
   *
   * <p>This function is typically called from {@link UserPropagator#initializeWithBackend} if the
   * theory solver needs to perform final consistency checks.
   */
  void notifyOnFinalCheck();
}
