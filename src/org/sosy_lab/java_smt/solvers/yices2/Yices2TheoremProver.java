/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_assert_formula;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_sat;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_sat_with_assumptions;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_model;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_unsat_core;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_pop;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_push;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_config;

import com.google.common.base.Preconditions;
import com.google.common.primitives.Ints;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;

class Yices2TheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private static final int DEFAULT_PARAMS = 0; // use default setting in the solver

  protected final Yices2FormulaCreator creator;
  protected final long curEnv;
  protected final long curCfg;

  private final Deque<Set<Integer>> constraintStack = new ArrayDeque<>();

  protected Yices2TheoremProver(
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pBmgr, pShutdownNotifier);
    this.creator = creator;
    // TODO get settings from SolverContext
    curCfg = yices_new_config();
    yices_set_config(curCfg, "solver-type", "dpllt");
    yices_set_config(curCfg, "mode", "push-pop");
    curEnv = yices_new_context(curCfg);
    // TODO config options
    constraintStack.push(new LinkedHashSet<>()); // initial level
  }

  boolean isClosed() {
    return closed;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    yices_pop(curEnv);
    constraintStack.pop();
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    int constraint = creator.extractInfo(pConstraint);
    yices_assert_formula(curEnv, constraint);
    constraintStack.peek().add(constraint);
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    yices_push(curEnv);
    constraintStack.push(new LinkedHashSet<>());
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    if (generateUnsatCores) {
      int[] allConstraints = getAllConstraints();
      return !yices_check_sat_with_assumptions(
          curEnv, DEFAULT_PARAMS, allConstraints.length, allConstraints);
    } else {
      return !yices_check_sat(curEnv, DEFAULT_PARAMS);
    }
  }

  private int[] getAllConstraints() {
    Set<Integer> allConstraints = new LinkedHashSet<>();
    constraintStack.forEach(allConstraints::addAll);
    return Ints.toArray(allConstraints);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    // TODO handle BooleanFormulaCollection / check for literals
    return !yices_check_sat_with_assumptions(
        curEnv, 0, pAssumptions.size(), uncapsulate(pAssumptions));
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return getModelWithoutChecks();
  }

  private List<BooleanFormula> encapsulate(int[] terms) {
    List<BooleanFormula> result = new ArrayList<>(terms.length);
    for (int t : terms) {
      result.add(creator.encapsulateBoolean(t));
    }
    return result;
  }

  private int[] uncapsulate(Collection<BooleanFormula> terms) {
    int[] result = new int[terms.size()];
    int i = 0;
    for (BooleanFormula t : terms) {
      result[i++] = creator.extractInfo(t);
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    return getUnsatCore0();
  }

  private List<BooleanFormula> getUnsatCore0() {
    return encapsulate(yices_get_unsat_core(curEnv));
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    Preconditions.checkState(!isClosed());
    checkGenerateUnsatCoresOverAssumptions();
    boolean sat =
        yices_check_sat_with_assumptions(
            curEnv, DEFAULT_PARAMS, pAssumptions.size(), uncapsulate(pAssumptions));
    return sat ? Optional.empty() : Optional.of(getUnsatCore0());
  }

  @Override
  public void close() {
    if (!closed) {
      yices_free_context(curEnv);
      yices_free_config(curCfg);
      constraintStack.clear();
      closed = true;
    }
  }

  @Override
  protected Model getModelWithoutChecks() {
    return new Yices2Model(yices_get_model(curEnv, 1), this, creator);
  }
}
