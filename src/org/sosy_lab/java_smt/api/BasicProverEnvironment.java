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

import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.CanIgnoreReturnValue;

import javax.annotation.Nullable;

/**
 * Super interface for {@link ProverEnvironment} and {@link InterpolatingProverEnvironment}
 * that provides only the common operations.
 * In most cases, just use one of the two sub-interfaces
 */
public interface BasicProverEnvironment<T> extends AutoCloseable {

  /**
   * Push a backtracking point and
   * add a formula to the environment stack, asserting it.
   * The return value may be used to identify this formula later on
   * in a query (this depends on the sub-type of the environment).
   */
  @Nullable
  @CanIgnoreReturnValue
  default T push(BooleanFormula f) {
    push();
    return addConstraint(f);
  }

  /**
   * Remove one formula from the environment stack.
   */
  void pop();

  /**
   * Add constraint to the context.
   */
  @Nullable
  @CanIgnoreReturnValue
  T addConstraint(BooleanFormula constraint);

  /**
   * Create backtracking point.
   */
  void push();

  /**
   * Check whether the conjunction of all formulas on the stack is unsatisfiable.
   */
  boolean isUnsat() throws SolverException, InterruptedException;

  /**
   * Get a satisfying assignment.
   * This should be called only immediately after an {@link #isUnsat()} call
   * that returned <code>false</code>.
   * A model might contain additional symbols with their evaluation,
   * if a solver uses its own temporary symbols.
   * There should be at least an value-assignment for each free symbol.
   */
  Model getModel() throws SolverException;

  /**
   * Get a list of satisfying assignments.
   * This is equivalent to <code>ImmutableList.copyOf(getModel())</code>,
   * but removes the need for calling {@link Model#close()}.
   *
   * <p>Note that if you need to iterate multiple times over the model
   * it may be more efficient to use this method instead of {@link #getModel()}
   * (depending on the solver).
   */
  ImmutableList<Model.ValueAssignment> getModelAssignments() throws SolverException;

  /**
   * Closes the prover environment.
   * The object should be discarded, and should not be used after closing.
   */
  @Override
  void close();
}
