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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
class Yices2TheoremProver extends AbstractProver<Void> implements ProverEnvironment {
  protected final Yices2FormulaCreator creator;
  protected final long curEnv;
  protected final long curCfg;
  protected boolean closed = false;

  protected Yices2TheoremProver(
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions) {
    super(pOptions);
    this.creator = creator;
    // TODO get settings from SolverContext
    curCfg = yices_new_config();
    yices_set_config(curCfg, "solver-type", "dpllt");
    yices_set_config(curCfg, "mode", "push-pop");
    curEnv = yices_new_context(curCfg);
    // TODO config options
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    yices_pop(curEnv);
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    yices_assert_formula(curEnv, creator.extractInfo(pConstraint));
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    yices_push(curEnv);
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    // ZERO if no params?
    Preconditions.checkState(!closed);
    return !yices_check_sat(curEnv, 0);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    int size = pAssumptions.size();
    Iterator<BooleanFormula> iterator = pAssumptions.iterator();
    int[] assumptions = new int[size];
    for (int i = 0; i < size; i++) {
      assumptions[i] = creator.extractInfo(iterator.next());
    } // TODO handle BooleanFormulaCollection / check for literals
    return !yices_check_sat_with_assumptions(curEnv, 0, size, assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new Yices2Model(yices_get_model(curEnv, 1), this, creator);
  }

  private List<BooleanFormula> encapsulate(int[] terms) {
    List<BooleanFormula> result = new ArrayList<>(terms.length);
    for (int t : terms) {
      result.add(creator.encapsulateBoolean(t));
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    int[] terms = yices_get_unsat_core(curEnv);
    return encapsulate(terms);
  }

  @Override
  public Optional<List<BooleanFormula>>
      unsatCoreOverAssumptions(Collection<BooleanFormula> pAssumptions)
          throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub
    if (!closed) {
      yices_free_context(curEnv);
      yices_free_config(curCfg);
      closed = true;
    }
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    return null;
  }

}
