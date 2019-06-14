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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.SExpr;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC4SLProver extends CVC4AbstractProver<Void> implements ProverEnvironment {

  private final Deque<Expr> assertedFormulas = new ArrayDeque<>();

  protected CVC4SLProver(CVC4FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    // TODO Auto-generated constructor stub
  }

  @Override
  public void pop() {
    // No actual push() cause CVC4 does not support separation login in incremental mode.
    assertedFormulas.pop();
  }

  @Override
  public Void push(BooleanFormula pF) {
    Expr exp = creator.extractInfo(pF);
    // No actual push() cause CVC4 does not support separation login in incremental mode.
    assertedFormulas.push(exp);
    return null;
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    Preconditions.checkState(!closed);
    Expr exp = creator.extractInfo(pConstraint);
    env.assertFormula(exp);
    return null;
  }



  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Optional<List<BooleanFormula>>
      unsatCoreOverAssumptions(Collection<BooleanFormula> pAssumptions)
          throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }



  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected CVC4Model getCVC4Model() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected void createConfig() {
    env.setOption("incremental", new SExpr(false));
    // smt.setLogic("QF_ALL_SUPPORTED");

  }

}
