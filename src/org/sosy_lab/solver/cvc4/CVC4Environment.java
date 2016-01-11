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

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Options;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;

import java.util.HashMap;
import java.util.Map;

public class CVC4Environment {

  private final ExprManager exprManager;
  private final Options options;

  private final Map<String, Expr> variablesCache = new HashMap<>();

  public CVC4Environment(Options pCvc4options) {
    options = pCvc4options;
    exprManager = new ExprManager(options);
  }

  public SmtEngine newSMTEngine() {
    SmtEngine smtEngine = new SmtEngine(exprManager);
    // TODO set options
    return smtEngine;
  }

  public ExprManager getExprManager() {
    return exprManager;
  }

  public Expr makeVariable(String name, Type type) {
    if (variablesCache.containsKey(name)) {
      Expr oldExp = variablesCache.get(name);
      assert type.equals(oldExp.getType());
      return oldExp;
    }

    Expr exp = exprManager.mkVar(name, type);
    variablesCache.put(name, exp);
    return exp;
  }
}
