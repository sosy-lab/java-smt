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
package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_all_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat_with_assumptions;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_free_termination_test;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_unsat_assumptions;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_unsat_core;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_last_error_message;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_option_checked;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_boolean_constant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_not;

import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.LongArrayBackedList;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.AllSatModelCallback;

/** Common base class for {@link Mathsat5TheoremProver} and {@link Mathsat5InterpolatingProver}. */
abstract class Mathsat5AbstractProver<T2> extends AbstractProver<T2> {

  protected final Mathsat5SolverContext context;
  protected final long curEnv;
  private final long curConfig;
  private final long terminationTest;
  protected final Mathsat5FormulaCreator creator;
  protected boolean closed = false;
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
    terminationTest = context.addTerminationTest(curEnv);
    shutdownNotifier = pShutdownNotifier;
  }

  private long buildConfig(Set<ProverOptions> opts) {
    Map<String, String> config = new LinkedHashMap<>();
    boolean generateUnsatCore =
        opts.contains(ProverOptions.GENERATE_UNSAT_CORE)
            || opts.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    config.put("model_generation", opts.contains(ProverOptions.GENERATE_MODELS) ? "true" : "false");
    config.put("unsat_core_generation", generateUnsatCore ? "1" : "0");
    if (generateUnsatCore) {
      config.put("theory.bv.eager", "false");
    }
    createConfig(config); // ask sub-classes for their options

    long cfg = msat_create_config();
    for (Entry<String, String> entry : config.entrySet()) {
      msat_set_option_checked(cfg, entry.getKey(), entry.getValue());
    }
    return cfg;
  }

  /** add needed options into the given map. */
  protected abstract void createConfig(Map<String, String> pConfig);

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    return !msat_check_sat(curEnv);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    checkForLiterals(pAssumptions);
    return !msat_check_sat_with_assumptions(curEnv, getMsatTerm(pAssumptions));
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

  @Override
  public Mathsat5Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new Mathsat5Model(getMsatModel(), creator, this);
  }

  /** @throws SolverException if an expected MathSAT failure occurs */
  protected long getMsatModel() throws SolverException {
    checkGenerateModels();
    return Mathsat5NativeApi.msat_get_model(curEnv);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    msat_pop_backtrack_point(curEnv);
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
      Collection<BooleanFormula> assumptions) {
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
  public void close() {
    if (!closed) {
      msat_destroy_env(curEnv);
      msat_free_termination_test(terminationTest);
      msat_destroy_config(curConfig);
      closed = true;
    }
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkGenerateAllSat();
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
          new LongArrayBackedList<>(model) {
            @Override
            protected BooleanFormula convert(long pE) {
              return creator.encapsulateBoolean(pE);
            }
          });
    }
  }
}
