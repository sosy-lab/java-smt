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

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.SmtEngine;

import org.sosy_lab.solver.Model;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.ProverEnvironment;

import java.util.List;

import javax.annotation.Nullable;

public class CVC4TheoremProver implements BasicProverEnvironment<Void>, ProverEnvironment {

  private final CVC4FormulaManager mgr;
  private final SmtEngine smtEngine;
  private boolean closed = false;

  protected CVC4TheoremProver(CVC4FormulaManager pMgr) {
    mgr = pMgr;
    smtEngine = pMgr.getEnvironment().newSMTEngine();
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
    smtEngine.assertFormula(mgr.extractInfo(pF));
    return null;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
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
    throw new UnsupportedOperationException("Not implemented");
    //    List<BooleanFormula> converted = new ArrayList<>();
    //    UnsatCore core = smtEngine.getUnsatCore();
    //    Iterator<?> it = core.iterator();
    //    while (it.hasNext()) {
    //      Object term = it.next();
    //    }
    //    return converted;
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    smtEngine.delete();
    closed = true;
  }

  @Override
  public <E extends Formula> E evaluate(E f) {
    throw new UnsupportedOperationException("CVC4 does not support evaluation");
  }

  @Override
  public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    throw new UnsupportedOperationException("Not implemented");
  }
}
