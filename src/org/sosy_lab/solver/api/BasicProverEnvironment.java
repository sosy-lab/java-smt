/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.api;

import org.sosy_lab.solver.Model;
import org.sosy_lab.solver.SolverException;

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
  T push(BooleanFormula f);

  /**
   * Remove one formula from the environment stack.
   */
  void pop();

  /**
   * Add constraint to the context.
   */
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
   */
  Model getModel() throws SolverException;

  /**
   * Closes the prover environment.
   * The object should be discarded, and should not be used after closing.
   */
  @Override
  void close();

  /**
   * Evaluate the formula with the previously generated model.
   * Assumes that model generation is enabled, and the previous call was
   * {@link #getModel}.
   * // TODO: provide a default for non-Z3 solvers.
   */
  <E extends Formula> E evaluate(E f);
}
