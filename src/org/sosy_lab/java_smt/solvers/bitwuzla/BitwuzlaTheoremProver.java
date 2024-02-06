// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
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
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaJNI.TerminationCallback;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaSolverContext.BitwuzlaSettings;

class BitwuzlaTheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private final long env;

  @SuppressWarnings("unused")
  private final BitwuzlaFormulaManager manager;

  private final BitwuzlaFormulaCreator creator;
  protected boolean wasLastSatCheckSat = false; // and stack is not changed

  private final TerminationCallback terminationCallback;
  private final long terminationCallbackHelper;

  protected BitwuzlaTheoremProver(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      BitwuzlaSettings pSettings,
      long pRandomSeed) {
    super(pOptions, pManager.getBooleanFormulaManager(), pShutdownNotifier);
    manager = pManager;
    creator = pCreator;
    // Bitwuzla guarantees that Terms and Sorts are shared
    env = createEnvironment(pOptions, pSettings, pRandomSeed);
    terminationCallback = shutdownNotifier::shouldShutdown;
    terminationCallbackHelper = addTerminationCallback();
  }

  private long createEnvironment(
      Set<ProverOptions> pFurtherOptions, BitwuzlaSettings pSettings, long pRandomSeed) {
    // TODO: set further options
    long options = BitwuzlaJNI.bitwuzla_options_new();

    if (pFurtherOptions.contains(ProverOptions.GENERATE_MODELS)
        || pFurtherOptions.contains(ProverOptions.GENERATE_ALL_SAT)) {
      BitwuzlaJNI.bitwuzla_set_option(
          options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS.swigValue(), 2);
    }

    if (pFurtherOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      BitwuzlaJNI.bitwuzla_set_option(
          options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_UNSAT_CORES.swigValue(), 2);
    }

    if (pFurtherOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      BitwuzlaJNI.bitwuzla_set_option(
          options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS.swigValue(), 2);
    }
    // TODO: termination callback
    // bitwuzlaJNI.bitwuzla_set_termination_callback();

    Preconditions.checkNotNull(pSettings.getSatSolver());
    BitwuzlaJNI.bitwuzla_set_option_mode(
        options,
        BitwuzlaOption.BITWUZLA_OPT_SAT_SOLVER.swigValue(),
        pSettings.getSatSolver().name().toLowerCase(Locale.getDefault()));
    BitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_SEED.swigValue(), pRandomSeed);
    // Stop Bitwuzla from rewriting formulas in outputs
    BitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_REWRITE_LEVEL.swigValue(), 0);

    // setFurtherOptions(pOptions, settings.getFurtherOptions());

    return BitwuzlaJNI.bitwuzla_new(options);
  }

  /**
   * Remove one backtracking point/level from the current stack. This removes the latest level
   * including all of its formulas, i.e., all formulas that were added for this backtracking point.
   */
  @Override
  public void popImpl() {
    BitwuzlaJNI.bitwuzla_pop(env, 1);
  }

  @Override
  public @Nullable Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    wasLastSatCheckSat = false;
    BitwuzlaJNI.bitwuzla_assert(env, ((BitwuzlaBooleanFormula) constraint).getTerm());
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
  public void pushImpl() throws InterruptedException {
    BitwuzlaJNI.bitwuzla_push(env, 1);
  }

  private boolean readSATResult(int resultValue) throws SolverException, InterruptedException {
    if (resultValue == BitwuzlaResult.BITWUZLA_SAT.swigValue()) {
      wasLastSatCheckSat = true;
      return false;
    } else if (resultValue == BitwuzlaResult.BITWUZLA_UNSAT.swigValue()) {
      return true;
    } else if (resultValue == BitwuzlaResult.BITWUZLA_UNKNOWN.swigValue()
        && terminationCallback.shouldTerminate()) {
      throw new InterruptedException("Bitwuzla interrupted.");
    } else {
      throw new SolverException("Bitwuzla returned UNKNOWN.");
    }
  }

  /** Check whether the conjunction of all formulas on the stack is unsatisfiable. */
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    wasLastSatCheckSat = false;
    ImmutableList.Builder<Long> builder = ImmutableList.builder();
    builder.addAll(BitwuzlaFormulaCreator.getVariableCasts());
    long[] arrayOfAssumptions = builder.build().stream().mapToLong(Long::longValue).toArray();
    final int result = BitwuzlaJNI.bitwuzla_check_sat_assuming(
        env,
        arrayOfAssumptions.length,
        arrayOfAssumptions);
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
    ImmutableList.Builder<Long> builder = ImmutableList.builder();
    builder.addAll(BitwuzlaFormulaCreator.getVariableCasts());
    for (BooleanFormula formula : assumptions) {
      BitwuzlaBooleanFormula bitwuzlaFormula = (BitwuzlaBooleanFormula) formula;
      builder.add(bitwuzlaFormula.getTerm());
    }
    long[] arrayOfAssumptions = builder.build().stream().mapToLong(Long::longValue).toArray();
    final int result = BitwuzlaJNI.bitwuzla_check_sat_assuming(
        env,
        arrayOfAssumptions.length,
        arrayOfAssumptions);
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
    return encapsulate(BitwuzlaJNI.bitwuzla_get_unsat_core(env, size), size[0]);
  }

  private List<BooleanFormula> encapsulate(long pTermsArray, long size) {
    List<BooleanFormula> result = new ArrayList<>((int) size);
    for (int i = 0; i < size; i++) {
      result.add(creator.encapsulateBoolean(BitwuzlaJNI.BitwuzlaTermArray_getitem(pTermsArray, i)));
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
    Preconditions.checkNotNull(assumptions);
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
      BitwuzlaJNI.free_termination(terminationCallbackHelper);
      BitwuzlaJNI.bitwuzla_delete(env);
      closed = true;
    }
    super.close();
  }

  @Override
  protected BitwuzlaModel getEvaluatorWithoutChecks() {
    return new BitwuzlaModel(
        env, this, creator, Collections2.transform(getAssertedFormulas(), creator::extractInfo));
  }

  public boolean isClosed() {
    return closed;
  }

  private long addTerminationCallback() {
    Preconditions.checkState(!closed, "solver context is already closed");
    return BitwuzlaJNI.set_termination(env, terminationCallback);
  }
}
