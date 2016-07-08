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
package org.sosy_lab.solver.api;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

/**
 * An interface to an incremental SMT solver
 * with methods for pushing and popping formulas as well as SAT checks.
 * Instances of this class can be used once for a series of related queries.
 * After that, the {@link #close} method should be called
 * (preferably using the try-with-resources syntax).
 * All methods are expected to throw {@link IllegalStateException}s after
 * close was called.
 *
 * <p>All solving methods are expected to throw {@link SolverException} if the solver
 * fails to solve the given query, and {@link InterruptedException} if a thread interrupt
 * was requested or a shutdown request via the {@link ShutdownNotifier}.
 * It is not guaranteed, though, that solvers respond in a timely manner (or at all)
 * to shutdown or interrupt requests.
 */
public interface ProverEnvironment extends BasicProverEnvironment<Void> {

  /**
   * Get an unsat core.
   * This should be called only immediately after an {@link #isUnsat()} call
   * that returned <code>false</code>.
   */
  List<BooleanFormula> getUnsatCore();

  /**
   * Get all satisfying assignments of the current environment with regards
   * to a subset of terms,
   * and create a region representing all those models.
   *
   * @param important A set of variables appearing in f.
   *     Only these variables will appear in the region.
   * @return A region representing all satisfying models of the formula.
   */
  <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException;

  /**
   * Check whether the conjunction of all formulas on the stack together with the
   * list of assumptions is satisfiable.
   *
   * @param assumptions A list of literals.
   */
  boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException;

  /**
   * Returns an UNSAT core (if it exists, otherwise {@code Optional.absent()}),
   * over the chosen assumptions.
   * Does NOT require the {@link ProverOptions#GENERATE_UNSAT_CORE} option to work.
   *
   * @param assumptions Selected assumptions
   * @return Empty optional if the constraints with assumptions are satisfiable,
   * subset of assumptions which is unsatisfiable with the original constraints otherwise.
   */
  Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException;

  /**
   * Interface for the {@link #allSat} callback.
   * @param <T> The result type of the callback, passed through by {@link #allSat}.
   */
  interface AllSatCallback<T> {

    /**
     * Callback for each possible satisfying assignment to given
     * {@code important} predicates.
     * If the predicate is assigned {@code true} in the model, it is returned
     * as-is in the list,
     * and otherwise it is negated.
     * TODO: this interface does not work properly for negated predicates.
     */
    void apply(List<BooleanFormula> model);

    /**
     * Returning the result generated after all the {@link #apply} calls have
     * went through.
     */
    T getResult() throws InterruptedException;
  }
}
