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


import com.google.common.base.Preconditions;
import edu.stanford.CVC4.Expr;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
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
import org.sosy_lab.java_smt.basicimpl.CachingModel;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;


class DReal4TheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private final DReal4FormulaCreator creator;
  private final Config config;
  private final Context curCnt;

  protected final Deque<List<DRealTerm<?, ?>>> assertedFormulas = new ArrayDeque<>();
  private Box model;

  protected DReal4TheoremProver(DReal4FormulaCreator creator, Set<ProverOptions> pOptions,
                                DReal4FormulaManager pFmgr, ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pFmgr.getBooleanFormulaManager(), pShutdownNotifier);
    this.creator = creator;
    config = creator.getEnv();
    model = new Box();
    assertedFormulas.push(new ArrayList<>());
    curCnt = new Context(config);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(size() > 0);
    assertedFormulas.pop();
    curCnt.Pop(1);
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint) throws InterruptedException {
    Preconditions.checkState(!closed);
    DRealTerm<?, ?> formula = creator.extractInfo(constraint);
    assertedFormulas.peek().add(formula);
    // It is not possible to assert an Expression, only Variable of type boolean or a formula
    Preconditions.checkState(!formula.isExp());
    if (formula.isVar()) {
      Preconditions.checkState(formula.getType() == Variable.Type.BOOLEAN);
      Formula f = new Formula(formula.getVariable());
      curCnt.declareVariables(f);
      curCnt.Assert(f);
      return null;
    } else {
      curCnt.declareVariables(formula.getFormula());
      curCnt.Assert(formula.getFormula());
      return null;
    }
  }


  @Override
  public void push() throws InterruptedException {
    Preconditions.checkState(!closed);
    assertedFormulas.push(new ArrayList<>());
    curCnt.Push(1);
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    return assertedFormulas.size() - 1;
  }
  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    boolean unsat = curCnt.CheckSat(model);
    return !unsat;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("dReal does not support isUnsatWSithAssumptions");
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException("dReal does not support getUnsatCore.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("dReal does not support unsatCoreOverAssumptions.");
  }

  @Override
  protected DReal4Model getEvaluatorWithoutChecks(){
    return new DReal4Model(this, creator, model, getAssertedExpressions());
  }

  @Override
  public void close() {
    if (!closed) {
      assertedFormulas.clear();
      Context.Exit();
      closed = true;
    }
  }

  protected Collection<DRealTerm<?, ?>> getAssertedExpressions() {
    List<DRealTerm<?, ?>> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }
}
