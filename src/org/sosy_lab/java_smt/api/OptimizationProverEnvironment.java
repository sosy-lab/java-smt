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

import org.sosy_lab.common.rationals.Rational;

import java.util.Optional;

/**
 * Interface for optimization modulo SMT.
 */
public interface OptimizationProverEnvironment extends BasicProverEnvironment<Void>, AutoCloseable {

  /**
   * Add the maximization <code>objective</code>.
   *
   * <b>Note: {@code push/pop} may be used for switching objectives</b>
   *
   * @return Objective handle, to be used for retrieving the value.
   */
  int maximize(Formula objective);

  /**
   * Add minimization <code>objective</code>.
   *
   * <b>Note: {@code push/pop} may be used for switching objectives</b>
   *
   * @return Objective handle, to be used for retrieving the value.
   */
  int minimize(Formula objective);

  /**
   * Optimize the objective function subject to the previously
   * imposed constraints.
   *
   * @return Status of the optimization problem.
   */
  OptStatus check() throws InterruptedException, SolverException;

  /**
   * @param epsilon Value to substitute for the {@code epsilon}.
   * @return Upper approximation of the optimized value, or
   *  absent optional if the objective is unbounded.
   */
  Optional<Rational> upper(int handle, Rational epsilon);

  /**
   * @param epsilon Value to substitute for the {@code epsilon}.
   * @return Lower approximation of the optimized value, or
   *  absent optional if the objective is unbounded.
   */
  Optional<Rational> lower(int handle, Rational epsilon);

  /**
   * Status of the optimization problem.
   */
  enum OptStatus {

    /**
     * The solution was found (may be unbounded).
     */
    OPT,

    /**
     * The set of constraints is unsatisfiable.
     */
    UNSAT,

    /**
     * The result is unknown.
     */
    UNDEF
  }
}
