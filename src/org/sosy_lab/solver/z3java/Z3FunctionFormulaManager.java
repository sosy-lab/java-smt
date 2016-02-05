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
package org.sosy_lab.solver.z3java;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.StringSymbol;

import org.sosy_lab.solver.basicimpl.AbstractFunctionFormulaManager;

import java.util.List;

class Z3FunctionFormulaManager
    extends AbstractFunctionFormulaManager<Expr, FuncDecl, Sort, Context> {

  private final Context z3context;

  Z3FunctionFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected Expr createUninterpretedFunctionCallImpl(FuncDecl funcDecl, List<Expr> pArgs) {
    return z3context.mkApp(funcDecl, pArgs.toArray(new Expr[] {}));
  }

  @Override
  protected FuncDecl declareUninterpretedFunctionImpl(
      String pName, Sort returnType, List<Sort> pArgTypes) {

    StringSymbol symbol = z3context.mkSymbol(pName);
    Sort[] sorts = pArgTypes.toArray(new Sort[] {});
    return z3context.mkFuncDecl(symbol, sorts, returnType);
  }
}
