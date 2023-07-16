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

package org.sosy_lab.java_smt.solvers.dreal4;


import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import java.util.Set;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;

class DReal4TheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private final DReal4FormulaCreator creator;
  private final Config curCfg;
  private final Context curCnt;
  protected DReal4TheoremProver(DReal4FormulaCreator creator, Set<ProverOptions> pOptions,
                                DReal4FormulaManager pFmgr, ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pFmgr.getBooleanFormulaManager(), pShutdownNotifier);
    this.creator = creator;
    curCfg = new Config();
    curCnt = new Context(curCfg);
  }

  @Override
  public void pop() {

  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint) throws InterruptedException {
    return null;
  }

  @Override
  public void push() throws InterruptedException {

  }

  @Override
  public int size() {
    return 0;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return false;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return false;
  }

  @Override
  public Model getModel() throws SolverException {
    return null;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return null;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return Optional.empty();
  }

  @Override
  protected Evaluator getEvaluatorWithoutChecks() throws SolverException {
    return null;
  }
}
