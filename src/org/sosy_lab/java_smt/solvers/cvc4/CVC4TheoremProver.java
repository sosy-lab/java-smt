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
import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.UnsatCore;

import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

import javax.annotation.Nullable;

public class CVC4TheoremProver implements BasicProverEnvironment<Void>, ProverEnvironment {

  private boolean closed = false;
  private final SmtEngine smtEngine;
  private final CVC4FormulaManager mgr;
  private final BooleanFormulaManager bfmgr;
  private final FormulaCreator<Expr, Type, CVC4Environment, Expr> creator;
  private final List<Expr> assertedFormulas = new ArrayList<>();

  protected CVC4TheoremProver(CVC4FormulaManager fMgr) {
    mgr       = fMgr;
    creator   = mgr.getFormulaCreator();
    bfmgr     = fMgr.getBooleanFormulaManager();
    smtEngine = fMgr.getEnvironment().newSMTEngine();
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
    Preconditions.checkState(!closed);
    Expr exp = mgr.extractInfo(pF);
    smtEngine.assertFormula(exp);
    assertedFormulas.add(exp);
    return null;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.remove(assertedFormulas.size() - 1);
    smtEngine.pop();
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Result result = smtEngine.checkSat();

    if (result.isNull() || result.isUnknown()) {
      throw new SolverException(
          "CVC4 returned null or unknown on sat check (" + result.toString() + ")");
    } else {
      if (result.isSat() == Result.Sat.SAT) {
        return false;
      } else if (result.isSat() == Result.Sat.UNSAT) {
        return true;
      } else {
        throw new SolverException("CVC4 returned unknown on sat check");
      }
    }
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
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    return new CVC4Model(smtEngine, creator, assertedFormulas);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    smtEngine.delete();
    closed = true;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    return null;
  }

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
}
