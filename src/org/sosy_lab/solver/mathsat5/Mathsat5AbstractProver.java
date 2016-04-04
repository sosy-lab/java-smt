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

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_free_termination_test;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_set_option_checked;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;

import java.util.Map;
import java.util.Map.Entry;

/**
 * Common base class for {@link Mathsat5TheoremProver}
 * and {@link Mathsat5InterpolatingProver}.
 */
abstract class Mathsat5AbstractProver<T2> implements BasicProverEnvironment<T2> {

  protected final Mathsat5SolverContext context;
  protected final long curEnv;
  private final long curConfig;
  private final long terminationTest;
  protected final Mathsat5FormulaCreator creator;
  protected boolean closed = false;

  protected Mathsat5AbstractProver(
      Mathsat5SolverContext pContext, Map<String, String> pConfig, Mathsat5FormulaCreator creator) {
    context = pContext;
    this.creator = creator;
    curConfig = buildConfig(pConfig);
    curEnv = context.createEnvironment(curConfig);
    terminationTest = context.addTerminationTest(curEnv);
  }

  private long buildConfig(Map<String, String> pConfig) {
    long cfg = msat_create_config();
    for (Entry<String, String> entry : pConfig.entrySet()) {
      msat_set_option_checked(cfg, entry.getKey(), entry.getValue());
    }
    return cfg;
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    try {
      return !msat_check_sat(curEnv);
    } catch (IllegalStateException e) {
      handleSolverExceptionInUnsatCheck(e);
      throw e;
    }
  }

  protected void handleSolverExceptionInUnsatCheck(IllegalStateException e) throws SolverException {
    String msg = Strings.nullToEmpty(e.getMessage());
    if (msg.contains("too many iterations")
        || msg.contains("impossible to build a suitable congruence graph!")
        || msg.contains("can't produce proofs")
        || msg.equals("msat_solve returned \"unknown\": unsupported")) {
      // This is not a bug in our code, but a problem of MathSAT which happens during interpolation
      throw new SolverException(e.getMessage(), e);
    }
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    return Mathsat5Model.create(creator, curEnv);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (Mathsat5Model model = Mathsat5Model.create(creator, curEnv)) {
      return model.generateAssignments();
    }
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    msat_pop_backtrack_point(curEnv);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    msat_destroy_env(curEnv);
    msat_free_termination_test(terminationTest);
    msat_destroy_config(curConfig);
    closed = true;
  }
}
