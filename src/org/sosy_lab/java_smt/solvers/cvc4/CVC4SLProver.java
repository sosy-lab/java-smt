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
import java.util.ArrayList;
import java.util.Set;
import javax.annotation.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public class CVC4SLProver extends CVC4AbstractProver<Void> implements ProverEnvironment {

  protected CVC4SLProver(
      CVC4FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr) {
    super(pFormulaCreator, pShutdownNotifier, pRandomSeed, pOptions, pBmgr);
  }

  @Override
  public void pop() {
    // No actual push() cause CVC4 does not support separation login in incremental mode.
    assertedFormulas.pop();
  }

  @Override
  public void push() {
    // No actual push() cause CVC4 does not support separation login in incremental mode.
    assertedFormulas.push(new ArrayList<>());
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula pF) {
    Preconditions.checkState(!closed);
    // No actual push() cause CVC4 does not support separation login in incremental mode.
    closeAllModels();
    Expr exp = creator.extractInfo(pF);
    smtEngine.assertFormula(importExpr(exp));
    assertedFormulas.peek().add(exp);
    return null;
  }

  @Override
  protected void setOptionForIncremental() {
    smtEngine.setOption("incremental", new SExpr(false));
    // smt.setLogic("QF_ALL_SUPPORTED");
  }
}
