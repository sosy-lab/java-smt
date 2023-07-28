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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class BitwuzlaTheoremProver implements ProverEnvironment {
  public BitwuzlaTheoremProver(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      long pEnv,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      AtomicBoolean pIsAnyStackAlive) {
  }

  /**
   * Remove one backtracking point/level from the current stack. This removes the latest level
   * including all of its formulas, i.e., all formulas that were added for this backtracking point.
   */
  @Override
  public void pop() {

  }

  /**
   * Add a constraint to the latest backtracking point.
   *
   * @param constraint
   */
  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint) throws InterruptedException {
    return null;
  }

  /**
   * Create a new backtracking point, i.e., a new level on the assertion stack. Each level can hold
   * several asserted formulas.
   *
   * <p>If formulas are added before creating the first backtracking point, they can not be removed
   * via a POP-operation.
   */
  @Override
  public void push() throws InterruptedException {

  }

  /**
   * Get the number of backtracking points/levels on the current stack.
   *
   * <p>Caution: This is the number of PUSH-operations, and not necessarily equal to the number of
   * asserted formulas. On any level there can be an arbitrary number of asserted formulas. Even
   * with size of 0, formulas can already be asserted (at bottom level).
   */
  @Override
  public int size() {
    return 0;
  }

  /**
   * Check whether the conjunction of all formulas on the stack is unsatisfiable.
   */
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return false;
  }

  /**
   * Check whether the conjunction of all formulas on the stack together with the list of
   * assumptions is satisfiable.
   *
   * @param assumptions A list of literals.
   */
  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return false;
  }

  /**
   * Get a satisfying assignment. This method should be called only immediately after an {@link
   * #isUnsat()} call that returned <code>false</code>. The returned model is guaranteed to stay
   * constant and valid as long as the solver context is available, even if constraints are added
   * to, pushed or popped from the prover stack.
   *
   * <p>A model might contain additional symbols with their evaluation, if a solver uses its own
   * temporary symbols. There should be at least a value-assignment for each free symbol.
   */
  @Override
  public Model getModel() throws SolverException {
    return null;
  }

  /**
   * Get an unsat core. This should be called only immediately after an {@link #isUnsat()} call that
   * returned <code>false</code>.
   */
  @Override
  public List<BooleanFormula> getUnsatCore() {
    return null;
  }

  /**
   * Returns an UNSAT core (if it exists, otherwise {@code Optional.empty()}), over the chosen
   * assumptions. Does NOT require the {@link ProverOptions#GENERATE_UNSAT_CORE} option to work.
   *
   * @param assumptions Selected assumptions
   * @return Empty optional if the constraints with assumptions are satisfiable, subset of
   * assumptions which is unsatisfiable with the original constraints otherwise.
   */
  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return Optional.empty();
  }

  /**
   * Closes the prover environment. The object should be discarded, and should not be used after
   * closing. The first call of this method will close the prover instance, further calls are
   * ignored.
   */
  @Override
  public void close() {

  }

  /**
   * Get all satisfying assignments of the current environment with regard to a subset of terms, and
   * create a region representing all those models.
   *
   * @param callback
   * @param important A set of (positive) variables appearing in the asserted queries. Only these
   *                  variables will appear in the region.
   * @return A region representing all satisfying models of the formula.
   */
  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return null;
  }
}
