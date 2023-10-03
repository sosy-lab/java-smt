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

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;
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
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBooleanFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaSolverContext.BitwuzlaSettings;

class BitwuzlaTheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private final long env;

  @SuppressWarnings("unused")
  private final BitwuzlaFormulaManager manager;

  private final BitwuzlaFormulaCreator creator;
  protected boolean wasLastSatCheckSat = false; // and stack is not changed

  protected BitwuzlaTheoremProver(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      BitwuzlaSettings pSettings,
      long pRandomSeed,
      AtomicBoolean pIsAnyStackAlive) {
    super(pOptions, pManager.getBooleanFormulaManager(), pShutdownNotifier);
    manager = pManager;
    creator = pCreator;
    // Bitwuzla guarantees that Terms and Sorts are shared
    env = createEnvironment(pOptions, pSettings, pRandomSeed);
  }

  private long createEnvironment(
      Set<ProverOptions> pFurtherOptions, BitwuzlaSettings pSettings, long pRandomSeed) {
    // TODO: set further options
    long options = bitwuzlaJNI.bitwuzla_options_new();

    if (pFurtherOptions.contains(ProverOptions.GENERATE_MODELS)) {
      bitwuzlaJNI.bitwuzla_set_option(
          options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS.swigValue(), 2);
    }
    // TODO: termination callback
    // bitwuzlaJNI.bitwuzla_set_termination_callback();

    Preconditions.checkNotNull(pSettings.getSatSolver());
    bitwuzlaJNI.bitwuzla_set_option_mode(
        options,
        BitwuzlaOption.BITWUZLA_OPT_SAT_SOLVER.swigValue(),
        pSettings.getSatSolver().name().toLowerCase(Locale.getDefault()));
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_SEED.swigValue(), pRandomSeed);
    // Stop Bitwuzla from rewriting formulas in outputs
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_REWRITE_LEVEL.swigValue(), 0);

    // setFurtherOptions(pOptions, settings.getFurtherOptions());

    return bitwuzlaJNI.bitwuzla_new(options);
  }

  /**
   * Remove one backtracking point/level from the current stack. This removes the latest level
   * including all of its formulas, i.e., all formulas that were added for this backtracking point.
   */
  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(size() > 0);
    bitwuzlaJNI.bitwuzla_pop(env, 1);
    super.pop();
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint) throws InterruptedException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    super.addConstraint(constraint);
    bitwuzlaJNI.bitwuzla_assert(env, ((BitwuzlaBooleanFormula) constraint).getTerm());
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
    Preconditions.checkState(!closed);
    super.push();
    bitwuzlaJNI.bitwuzla_push(env, 1);
  }

  private boolean readSATResult(int resultValue) throws SolverException {
    if (resultValue == BitwuzlaResult.BITWUZLA_SAT.swigValue()) {
      wasLastSatCheckSat = true;
      return false;
    } else if (resultValue == BitwuzlaResult.BITWUZLA_UNSAT.swigValue()) {
      return true;
    } else {
      throw new SolverException("Bitwuzla returned UNKNOWN.");
    }
  }

  /** Check whether the conjunction of all formulas on the stack is unsatisfiable. */
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    final int result = bitwuzlaJNI.bitwuzla_check_sat(env);
    return readSATResult(result);
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
    int size = assumptions.size();
    long[] bitwuzlaAssumptions = new long[size];
    BooleanFormula[] inputAssumptions = assumptions.toArray(new BooleanFormula[0]);
    for (int i = 0; i < size; i++) {
      bitwuzlaAssumptions[i] = ((BitwuzlaBooleanFormula) inputAssumptions[i]).getTerm();
    }
    final int result = bitwuzlaJNI.bitwuzla_check_sat_assuming(env, size, bitwuzlaAssumptions);
    return readSATResult(result);
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
    Preconditions.checkState(!closed);
    Preconditions.checkState(wasLastSatCheckSat, NO_MODEL_HELP);
    checkGenerateModels();
    Model result = new CachingModel(getEvaluatorWithoutChecks());
    return result;
  }

  private List<BooleanFormula> getUnsatCore0() {
    long[] size = new long[1];
    return encapsulate(bitwuzlaJNI.bitwuzla_get_unsat_core(env, size), size[0]);
  }

  private List<BooleanFormula> encapsulate(long pTermsArray, long size) {
    List<BooleanFormula> result = new ArrayList<>((int) size);
    for (int i = 0; i < size; i++) {
      result.add(creator.encapsulateBoolean(bitwuzlaJNI.BitwuzlaTermArray_getitem(pTermsArray, i)));
    }
    return result;
  }

  /**
   * Get an unsat core. This should be called only immediately after an {@link #isUnsat()} call that
   * returned <code>false</code>.
   */
  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    Preconditions.checkState(!wasLastSatCheckSat);
    return getUnsatCore0();
  }

  /**
   * Returns an UNSAT core (if it exists, otherwise {@code Optional.empty()}), over the chosen
   * assumptions. Does NOT require the {@link ProverOptions#GENERATE_UNSAT_CORE} option to work.
   *
   * @param assumptions Selected assumptions
   * @return Empty optional if the constraints with assumptions are satisfiable, subset of
   *     assumptions which is unsatisfiable with the original constraints otherwise.
   */
  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    Preconditions.checkState(!wasLastSatCheckSat);
    boolean sat = !isUnsatWithAssumptions(assumptions);
    return sat ? Optional.empty() : Optional.of(getUnsatCore0());
  }

  /**
   * Closes the prover environment. The object should be discarded, and should not be used after
   * closing. The first call of this method will close the prover instance, further calls are
   * ignored.
   */
  @Override
  public void close() {
    if (!closed) {
      bitwuzlaJNI.bitwuzla_delete(env);
      closed = true;
    }
    super.close();
  }

  //  /**
  //   * Get all satisfying assignments of the current environment with regard to a subset of terms,
  // and
  //   * create a region representing all those models.
  //   *
  //   * @param callback
  //   * @param important A set of (positive) variables appearing in the asserted queries. Only
  // these
  //   *     variables will appear in the region.
  //   * @return A region representing all satisfying models of the formula.
  //   */
  //  @Override
  //  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
  //      throws InterruptedException, SolverException {
  //    return null;
  //  }

  @Override
  protected BitwuzlaModel getEvaluatorWithoutChecks() {
    return new BitwuzlaModel(
        env, this, creator, Collections2.transform(getAssertedFormulas(), creator::extractInfo));
  }
}
