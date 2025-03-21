// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_all_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat_with_assumptions;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_free_termination_callback;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_search_stats;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_unsat_assumptions;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_unsat_core;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_last_error_message;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_num_backtrack_points;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_option_checked;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_termination_callback;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_boolean_constant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_not;

import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.primitives.Longs;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.AllSatModelCallback;

/** Common base class for {@link Mathsat5TheoremProver} and {@link Mathsat5InterpolatingProver}. */
abstract class Mathsat5AbstractProver<T2> extends AbstractProver<T2> {

  protected final Mathsat5SolverContext context;
  protected final long curEnv;
  private final long curConfig;
  protected final Mathsat5FormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;

  protected Mathsat5AbstractProver(
      Mathsat5SolverContext pContext,
      Set<ProverOptions> pOptions,
      Mathsat5FormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions);
    context = pContext;
    creator = pCreator;
    curConfig = buildConfig(pOptions);
    curEnv = context.createEnvironment(curConfig);
    shutdownNotifier = pShutdownNotifier;
  }

  private long buildConfig(Set<ProverOptions> opts) {
    Map<String, String> config = new LinkedHashMap<>();
    boolean generateUnsatCore =
        opts.contains(ProverOptions.GENERATE_UNSAT_CORE)
            || opts.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    config.put("model_generation", opts.contains(ProverOptions.GENERATE_MODELS) ? "true" : "false");
    config.put("unsat_core_generation", generateUnsatCore ? "1" : "0");
    config.put("proof_generation", opts.contains(ProverOptions.GENERATE_PROOFS) ? "true" : "false");
    if (generateUnsatCore) {
      config.put("theory.bv.eager", "false");
    }
    createConfig(config); // ask sub-classes for their options

    long cfg = msat_create_config();
    for (Map.Entry<String, String> entry : config.entrySet()) {
      msat_set_option_checked(cfg, entry.getKey(), entry.getValue());
    }
    return cfg;
  }

  /** add needed options into the given map. */
  protected abstract void createConfig(Map<String, String> pConfig);

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    final long hook = msat_set_termination_callback(curEnv, context.getTerminationTest());
    try {
      return !msat_check_sat(curEnv);
    } finally {
      msat_free_termination_callback(hook);
    }
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    checkForLiterals(pAssumptions);

    final long hook = msat_set_termination_callback(curEnv, context.getTerminationTest());
    try {
      return !msat_check_sat_with_assumptions(curEnv, getMsatTerm(pAssumptions));
    } finally {
      msat_free_termination_callback(hook);
    }
  }

  private void checkForLiterals(Collection<BooleanFormula> formulas) {
    for (BooleanFormula f : formulas) {
      long t = getMsatTerm(f);
      if (msat_term_is_boolean_constant(curEnv, t)) {
        // boolean constant is valid
      } else if (msat_term_is_not(curEnv, t)
          && msat_term_is_boolean_constant(curEnv, msat_term_get_arg(t, 0))) {
        // negated boolean constant is valid
      } else {
        throw new UnsupportedOperationException("formula is not a (negated) literal: " + f);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new CachingModel(new Mathsat5Model(getMsatModel(), creator, this));
  }

  /**
   * @throws SolverException if an expected MathSAT failure occurs
   */
  protected long getMsatModel() throws SolverException {
    checkGenerateModels();
    return Mathsat5NativeApi.msat_get_model(curEnv);
  }

  @SuppressWarnings("resource")
  @Override
  public Evaluator getEvaluator() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return registerEvaluator(new Mathsat5Evaluator(this, creator, curEnv));
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    msat_push_backtrack_point(curEnv);
  }

  @Override
  protected void popImpl() {
    closeAllEvaluators();
    msat_pop_backtrack_point(curEnv);
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(
        msat_num_backtrack_points(curEnv) == super.size(),
        "prover-size %s does not match stack-size %s",
        msat_num_backtrack_points(curEnv),
        super.size());
    return super.size();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    long[] terms = msat_get_unsat_core(curEnv);
    return encapsulate(terms);
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    Preconditions.checkNotNull(assumptions);
    closeAllEvaluators();

    if (!isUnsatWithAssumptions(assumptions)) {
      return Optional.empty();
    }

    long[] unsatAssumptions = msat_get_unsat_assumptions(curEnv);
    return Optional.of(encapsulate(unsatAssumptions));
  }

  private List<BooleanFormula> encapsulate(long[] terms) {
    List<BooleanFormula> result = new ArrayList<>(terms.length);
    for (long t : terms) {
      result.add(creator.encapsulateBoolean(t));
    }
    return result;
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    // Mathsat sigsevs if you try to get statistics for closed environments
    Preconditions.checkState(!closed);
    final String stats = msat_get_search_stats(curEnv);
    return ImmutableMap.copyOf(
        Splitter.on("\n").trimResults().omitEmptyStrings().withKeyValueSeparator(" ").split(stats));
  }

  @Override
  public void close() {
    if (!closed) {
      msat_destroy_env(curEnv);
      msat_destroy_config(curConfig);
    }
    super.close();
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkGenerateAllSat();
    closeAllEvaluators();

    long[] imp = new long[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      imp[i++] = getMsatTerm(impF);
    }
    MathsatAllSatCallback<T> uCallback = new MathsatAllSatCallback<>(callback);
    push();
    int numModels = msat_all_sat(curEnv, imp, uCallback);
    pop();

    if (numModels == -1) {
      throw new SolverException(
          "Error occurred during Mathsat allsat: " + msat_last_error_message(curEnv));

    } else if (numModels == -2) {
      // Formula is trivially tautological.
      // With the current API, we have no way of signaling this except by iterating over all 2^n
      // models, which is probably not what we want.
      throw new UnsupportedOperationException("allSat for trivially tautological formula");
    }
    return callback.getResult();
  }

  class MathsatAllSatCallback<T> implements AllSatModelCallback {
    private final AllSatCallback<T> clientCallback;

    MathsatAllSatCallback(AllSatCallback<T> pClientCallback) {
      clientCallback = pClientCallback;
    }

    @Override
    public void callback(long[] model) throws InterruptedException {
      shutdownNotifier.shutdownIfNecessary();
      clientCallback.apply(
          Collections.unmodifiableList(
              Lists.transform(Longs.asList(model), creator::encapsulateBoolean)));
    }
  }
}
