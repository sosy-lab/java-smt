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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.UnsatCore;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

import javax.annotation.Nullable;

public class CVC4TheoremProver extends CVC4SolverBasedProver<Void> implements ProverEnvironment {

  private final CVC4FormulaManager mgr;
  private final SmtEngine smtEngine;
  private final BooleanFormulaManager bfmgr;
  private boolean closed = false;
  private final List<Expr> assertedFormulas = new ArrayList<>();

  protected CVC4TheoremProver(CVC4FormulaCreator creator, CVC4FormulaManager pMgr) {
    super(creator);
    mgr = pMgr;
    smtEngine = creator.getSmtEngine();
    bfmgr = pMgr.getBooleanFormulaManager();
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    smtEngine.push();
  }

  @Override
  public Void push(BooleanFormula pF) {
    push();
    return addConstraint(pF);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula pF) {
    super.addConstraint0(pF);
    return null;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.remove(assertedFormulas.size() - 1);
    smtEngine.pop();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    List<BooleanFormula> converted = new ArrayList<>();
    UnsatCore core = smtEngine.getUnsatCore();
    for (Expr aCore : core) {
      converted.add(mgr.encapsulateBooleanFormula(aCore));
    }
    return converted;
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
//    smtEngine.delete();
    closed = true;
  }

//  @Override
//  public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
//      throws InterruptedException, SolverException {
//    Preconditions.checkState(!closed);
//    // Unpack formulas to terms.
//    Expr[] importantFormulas = new Expr[pImportant.size()];
//    int i = 0;
//    for (BooleanFormula impF : pImportant) {
//      importantFormulas[i++] = getCVC4Expr(impF);
//    }
//
//    smtEngine.push();
//
//    while (!isUnsat()) {
//      Expr[] valuesOfModel = new Expr[importantFormulas.length];
//      CVC4Model model = new CVC4Model(smtEngine, creator, assertedFormulas);
//
//      for (int j = 0; j < importantFormulas.length; j++) {
//        Object valueOfExpr = model.evaluateImpl(importantFormulas[j]);
//
//        if (valueOfExpr instanceof Boolean && !((Boolean) valueOfExpr)) {
//          valuesOfModel[j] =
//              getCVC4Expr(bfmgr.not(mgr.encapsulateBooleanFormula(importantFormulas[j])));
//        } else {
//          valuesOfModel[j] = importantFormulas[j];
//        }
//      }
//
//      List<BooleanFormula> wrapped =
//          Lists.transform(Arrays.asList(valuesOfModel), creator.encapsulateBoolean);
//      pCallback.apply(wrapped);
//
//      BooleanFormula negatedModel = bfmgr.not(bfmgr.and(wrapped));
//      smtEngine.assertFormula(getCVC4Expr(negatedModel));
//    }
//
//    // we pushed some levels on assertionStack, remove them and delete solver
//    smtEngine.pop();
//    return pCallback.getResult();
//  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    return null;
  }
}
