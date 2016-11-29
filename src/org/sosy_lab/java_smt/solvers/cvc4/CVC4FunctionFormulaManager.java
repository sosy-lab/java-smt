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

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.FunctionType;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.acsys.CVC4.vectorType;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

import java.util.List;

public class CVC4FunctionFormulaManager
    extends AbstractUFManager<Expr, Expr, Type, ExprManager> {

  private final ExprManager exprManager;

  protected CVC4FunctionFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getExprManager();
  }

  @Override
  protected Expr declareUninterpretedFunctionImpl(
      String pName, Type pReturnType, List<Type> pArgTypes) {
    vectorType argTypes = new vectorType();
    for (Type t : pArgTypes) {
      argTypes.add(t);
    }
    FunctionType functionType = exprManager.mkFunctionType(argTypes, pReturnType);
    return formulaCreator.makeVariable(functionType, pName);
  }

  @Override
  protected Expr createUninterpretedFunctionCallImpl(Expr pFunc, List<Expr> pArgs) {
    vectorExpr args = new vectorExpr();
    for (Expr t : pArgs) {
      args.add(t);
    }
    return exprManager.mkExpr(Kind.APPLY_UF, pFunc, args);
  }
}
