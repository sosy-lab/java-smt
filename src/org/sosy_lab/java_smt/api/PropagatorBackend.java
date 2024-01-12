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
   * Similarly, equalities between registered expressions are reported via
   * {@link UserPropagator#onEquality} (if enabled via
   * {@link #notifyOnEquality()}.
   * @param theoryExpr The expression to observe.
   */
  void registerExpression(BooleanFormula theoryExpr);

  /**
   * Raises a conflict caused by a set of conflicting assignments. Shall only be called
   * from within a callback by {@link UserPropagator} such as
   * {@link UserPropagator#onKnownValue} and
   * {@link UserPropagator#onFinalCheck()}.
   *
   * <p> Effectively causes the solver to learn the implication "/\ conflictLiterals => false"
   *
   * @param conflictLiterals A set of inconsistent assignments.
   */
  void propagateConflict(BooleanFormula[] conflictLiterals);

  /**
   * Propagates a consequence implied by a set of assigned literals. Shall only be called
   * from within a callback by {@link UserPropagator} such as
   * {@link UserPropagator#onKnownValue} and
   * {@link UserPropagator#onFinalCheck()}.
   *
   * <p> Effectively causes the solver to learn the implication "/\ assignedLiterals => consequence"
   *
   * @param assignedLiterals A set of assigned literals.
   * @param consequence The consequence implied by the assigned literals.
   */
  void propagateConsequence(BooleanFormula[] assignedLiterals, BooleanFormula consequence);

  /**
   * Propagates a consequence as well as a set of equalities implied by a set of assigned literals.
   * Shall only be called from within a callback by {@link UserPropagator} such as
   * {@link UserPropagator#onKnownValue} and
   * {@link UserPropagator#onFinalCheck()}
   *
   * <p> Effectively causes the solver to learn the implication "/\ assignedLiterals =>
   *    (consequence /\ forall i: equalitiesLHS[i] == equalitiesRHS[i])"
   *
   * @param assignedLiterals A set of assigned literals.
   * @param equalitiesLHS The left-hand sides of implied equalities.
   * @param equalitiesRHS The right-hand sides of implied equalities.
   * @param consequence The consequence implied by the assigned literals.
   */
  void propagateConsequenceWithEqualities(BooleanFormula[] assignedLiterals,
                                          BooleanFormula[] equalitiesLHS,
                                          BooleanFormula[] equalitiesRHS,
                                          BooleanFormula consequence);

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
   * Enables tracking of equalities for the associated {@link UserPropagator} via
   * {@link UserPropagator#onEquality(BooleanFormula, BooleanFormula)}.
   *
   * <p>This function is typically called from {@link UserPropagator#initialize()} if the
   * theory solver needs to observe equalities between expressions registered by
   * {@link #registerExpression}.
   */
  void notifyOnEquality();

  /**
   * Enables the final callback {@link UserPropagator#onFinalCheck()} that is invoked
   * when the solver finds a full satisfying assignment.
   *
   * <p>This function is typically called from {@link UserPropagator#initialize()} if the
   * theory solver needs to perform final consistency checks.
   */
  void notifyOnFinalCheck();
}
