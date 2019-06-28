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
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;
import org.sosy_lab.java_smt.basicimpl.AbstractSLFormulaManager;

public class CVC4SLFormulaManager extends AbstractSLFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  protected CVC4SLFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getEnv();
  }

  @Override
  protected Expr makeStar(Expr e1, Expr e2) {
    return exprManager.mkExpr(Kind.SEP_STAR, e1, e2);
  }

  @Override
  protected Expr makePointsTo(Expr pPtr, Expr pTo) {
    return exprManager.mkExpr(Kind.SEP_PTO, pPtr, pTo);
  }

  @Override
  protected Expr makeMagicWand(Expr pE1, Expr pE2) {
    return exprManager.mkExpr(Kind.SEP_WAND, pE1, pE2);
  }

  @Override
  protected Expr makeEmptyHeap(Type pT1, Type pT2) {
    return exprManager.mkExpr(Kind.SEP_EMP, pT1.mkGroundTerm(), pT2.mkGroundTerm());
  }

  @Override
  protected Expr makeNilElement(Type pType) {
    return exprManager.mkExpr(Kind.SEP_NIL, pType.mkGroundTerm());
  }
}
