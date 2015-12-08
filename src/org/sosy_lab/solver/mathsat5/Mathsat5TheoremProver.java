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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_all_sat;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_unsat_core;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_last_error_message;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_option_checked;

import com.google.common.base.Preconditions;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.LongArrayBackedList;
import org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.AllSatModelCallback;

import java.util.ArrayList;
import java.util.List;

import javax.annotation.Nullable;

class Mathsat5TheoremProver extends Mathsat5AbstractProver<Void> implements ProverEnvironment {

  private static final boolean USE_SHARED_ENV = true;

  Mathsat5TheoremProver(
      Mathsat5FormulaManager pMgr, boolean generateModels, boolean generateUnsatCore) {
    super(pMgr, createConfig(generateModels, generateUnsatCore), USE_SHARED_ENV, true);
  }

  private static long createConfig(boolean generateModels, boolean generateUnsatCore) {
    long cfg = msat_create_config();
    if (generateModels) {
      msat_set_option_checked(cfg, "model_generation", "true");
    }
    if (generateUnsatCore) {
      msat_set_option_checked(cfg, "unsat_core_generation", "1");
    }
    return cfg;
  }

  @Override
  public @Nullable Void push(BooleanFormula f) {
    Preconditions.checkState(!closed);
    push();
    addConstraint(f);
    return null;
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    msat_assert_formula(curEnv, getMsatTerm(constraint));
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    msat_push_backtrack_point(curEnv);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    long[] terms = msat_get_unsat_core(curEnv);
    List<BooleanFormula> result = new ArrayList<>(terms.length);
    for (long t : terms) {
      result.add(mgr.encapsulateBooleanFormula(t));
    }
    return result;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    long[] imp = new long[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      imp[i++] = getMsatTerm(impF);
    }
    MathsatAllSatCallback<T> uCallback = new MathsatAllSatCallback<>(callback);
    int numModels = msat_all_sat(curEnv, imp, uCallback);

    if (numModels == -1) {
      throw new RuntimeException(
          "Error occurred during Mathsat allsat: " + msat_last_error_message(curEnv));

    } else if (numModels == -2) {
      throw new SolverException("Number of models should be finite with boolean predicates");
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
      clientCallback.apply(
          new LongArrayBackedList<BooleanFormula>(model) {
            @Override
            protected BooleanFormula convert(long pE) {
              return mgr.encapsulateBooleanFormula(pE);
            }
          });
    }
  }
}
