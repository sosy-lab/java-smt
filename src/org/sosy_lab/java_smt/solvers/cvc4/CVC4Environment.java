/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.UnsatCore;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.common.ShutdownNotifier;

public class CVC4Environment {

  private final ExprManager exprManager;
  private SmtEngine smtEngine;
  private final ShutdownNotifier shutdownNotifier;
  private AtomicBoolean interrupted;

  public CVC4Environment(
      ExprManager pExprManager, int randomSeed, ShutdownNotifier pShutdownNotifier) {
    exprManager = pExprManager;
    shutdownNotifier = pShutdownNotifier;
    interrupted = new AtomicBoolean(false);
    smtEngine = new SmtEngine(exprManager);
    smtEngine.setOption("incremental", new SExpr(true));
    smtEngine.setOption("produce-models", new SExpr(true));
    smtEngine.setOption("produce-assertions", new SExpr(true));
    smtEngine.setOption("dump-models", new SExpr(true));
    // smtEngine.setOption("produce-unsat-cores", new SExpr(true));
    smtEngine.setOption("output-language", new SExpr("smt2"));
    smtEngine.setOption("random-seed", new SExpr(randomSeed));
    shutdownNotifier.register(
        (reason) -> {
          interrupted.set(true);
          while (interrupted.get()) {
            smtEngine.interrupt();
            // Due to a bug in CVC4, smtEngine.interrupt() has no effect when it is called too soon.
            // For example in the case of smtEngine.checkSat(), this is if interrupt() is called
            // before the line "Result result = d_propEngine->checkSat();" is called in the CVC4 C++
            // method SmtEngine::check(), which seems to take about 10 ms. When this is fixed in
            // CVC4, we can remove the Thread.sleep(10), the AtomicBoolean interrupted and the while
            // loop surrounding this block.
            try {
              Thread.sleep(10);
            } catch (InterruptedException e) {
            }
          }
        });
  }

  public ExprManager getExprManager() {
    return exprManager;
  }

  public void push() {
    smtEngine.push();
  }

  public void assertFormula(Expr pExp) {
    smtEngine.assertFormula(pExp);
  }

  public Result checkSat() {
    Result result = smtEngine.checkSat();
    if (interrupted.get()) {
      interrupted.set(false);
    }
    return result;
  }

  public void delete() {
    smtEngine.delete();
  }

  public UnsatCore getUnsatCore() {
    return smtEngine.getUnsatCore();
  }

  public void pop() {
    smtEngine.pop();
  }

  public Expr getValue(Expr pExp) {
    return smtEngine.getValue(pExp);
  }
}
