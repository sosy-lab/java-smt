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

import edu.nyu.acsys.CVC4.UnsatCore;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.ProverEnvironment;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class CVC4TheoremProver extends CVC4AbstractProver<Void> implements ProverEnvironment {

  protected CVC4TheoremProver(CVC4FormulaManager pMgr) {
    super(pMgr);
  }

  @Override
  public Void push(BooleanFormula pF) {
    Preconditions.checkState(!closed);
    smtEngine.push();
    smtEngine.assertFormula(mgr.extractInfo(pF));
    return null;
  }

  @Override
  public Void addConstraint(BooleanFormula pF) {
    Preconditions.checkState(!closed);
    smtEngine.assertFormula(mgr.extractInfo(pF));
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    smtEngine.push();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    List<BooleanFormula> converted = new ArrayList<>();
    UnsatCore core = smtEngine.getUnsatCore();
    Iterator<?> it = core.iterator();
    while (it.hasNext()) {
      Object term = it.next();
    }
    return converted;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO
    return null;
  }
}
