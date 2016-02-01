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
package org.sosy_lab.solver.cvc4;

import static org.sosy_lab.solver.cvc4.CVC4FormulaManager.getCVC4Expr;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.UnsatCore;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import javax.annotation.Nullable;

public class CVC4TheoremProver implements BasicProverEnvironment<Void>, ProverEnvironment {

  private final CVC4FormulaManager mgr;
  private final SmtEngine smtEngine;
  private final BooleanFormulaManager bfmgr;
  private final FormulaCreator<Expr, Type, CVC4Environment> creator;
  private boolean closed = false;
  private final List<Expr> assertedFormulas = new ArrayList<>();

  protected CVC4TheoremProver(CVC4FormulaManager pMgr) {
    mgr = pMgr;
    smtEngine = pMgr.getEnvironment().newSMTEngine();
    creator = mgr.getFormulaCreator();
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
    Preconditions.checkState(!closed);
    // Unpack formulas to terms.
    Expr[] importantFormulas = new Expr[pImportant.size()];
    int i = 0;
    for (BooleanFormula impF : pImportant) {
      importantFormulas[i++] = getCVC4Expr(impF);
    }

    smtEngine.push();

    while (!isUnsat()) {
      Expr[] valuesOfModel = new Expr[importantFormulas.length];
      CVC4Model model = new CVC4Model(smtEngine, creator, assertedFormulas);

      for (int j = 0; j < importantFormulas.length; j++) {
        Object valueOfExpr = model.evaluateImpl(importantFormulas[j]);

        if (valueOfExpr instanceof Boolean && !((Boolean) valueOfExpr)) {
          valuesOfModel[j] =
              getCVC4Expr(bfmgr.not(mgr.encapsulateBooleanFormula(importantFormulas[j])));
        } else {
          valuesOfModel[j] = importantFormulas[j];
        }
      }

      List<BooleanFormula> wrapped =
          Lists.transform(Arrays.asList(valuesOfModel), creator.encapsulateBoolean);
      pCallback.apply(wrapped);

      BooleanFormula negatedModel = bfmgr.not(bfmgr.and(wrapped));
      smtEngine.assertFormula(getCVC4Expr(negatedModel));
    }

    // we pushed some levels on assertionStack, remove them and delete solver
    smtEngine.pop();
    return pCallback.getResult();
  }
}
