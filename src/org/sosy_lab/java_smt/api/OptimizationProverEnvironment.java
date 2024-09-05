// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;

/** Interface for optimization modulo SMT. */
public interface OptimizationProverEnvironment extends BasicProverEnvironment<Formula>,
                                                       AutoCloseable {

  /**
   * Add the maximization <code>objective</code>.
   *
   * <p><b>Note: {@code push/pop} may be used for switching objectives</b>
   *
   * @return Objective handle, to be used for retrieving the value.
   */
  int maximize(Formula objective);

  /**
   * Add minimization <code>objective</code>.
   *
   * <p><b>Note: {@code push/pop} may be used for switching objectives</b>
   *
   * @return Objective handle, to be used for retrieving the value.
   */
  int minimize(Formula objective);

  /**
   * Optimize the objective function subject to the previously imposed constraints.
   *
   * @return Status of the optimization problem.
   */
  OptStatus check() throws InterruptedException, SolverException;

  /**
   * @param epsilon Value to substitute for the {@code epsilon}.
   * @return Upper approximation of the optimized value, or absent optional if the objective is
   *     unbounded.
   */
  Optional<Rational> upper(int handle, Rational epsilon);

  /**
   * @param epsilon Value to substitute for the {@code epsilon}.
   * @return Lower approximation of the optimized value, or absent optional if the objective is
   *     unbounded.
   */
  Optional<Rational> lower(int handle, Rational epsilon);

  /**
   * {@inheritDoc}
   *
   * <p>Please note that the prover is allowed to use standard numbers for any real variable in the
   * model after a sat-query returned {@link OptStatus#OPT}. For integer formulas, we expect the
   * optimal assignment.
   *
   * <p>Example 1: For the constraint 'x&lt;10' with a real x, the upper bound of x is '10-epsilon'
   * (epsilon can even be set to zero). The model can return the assignment x=9. To get an optimal
   * assignment, query the solver with an additional constraint 'x == 10-epsilon'.
   *
   * <p>Example 2: For the constraint 'x&lt;10' with an integer x, the upper bound of x is '9'
   * (epsilon is irrelevant here and can be zero). The model returns the optimal assignment x=9.
   */
  @Override
  Model getModel() throws SolverException;

  /** Status of the optimization problem. */
  enum OptStatus {

    /** The solution was found (may be unbounded). */
    OPT,

    /** The set of constraints is unsatisfiable. */
    UNSAT,

    /** The result is unknown. */
    UNDEF
  }
}
