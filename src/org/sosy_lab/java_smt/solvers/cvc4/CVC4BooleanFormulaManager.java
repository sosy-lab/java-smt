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
import edu.nyu.acsys.CVC4.vectorExpr;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

import java.util.Collection;

public class CVC4BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Expr, Type, CVC4Environment, Expr> {

  private final ExprManager em;
  private final CVC4Environment env;

  protected CVC4BooleanFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    env = pCreator.getEnv();
    em = env.getExprManager();
  }

  @Override
  protected Expr makeVariableImpl(String pVar) {
    return env.makeVariable(pVar, getFormulaCreator().getBoolType());
  }

  @Override
  protected Expr makeBooleanImpl(boolean pValue) {
    return em.mkConst(pValue);
  }

  @Override
  protected Expr not(Expr pParam1) {
    return em.mkExpr(Kind.NOT, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    return em.mkExpr(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Expr andImpl(Collection<Expr> pParams) {
    vectorExpr vExpr = new vectorExpr();
    for (Expr e : pParams) {
      vExpr.add(e);
    }
    return em.mkExpr(Kind.AND, vExpr);
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    return em.mkExpr(Kind.OR, pParam1, pParam2);
  }

  @Override
  protected Expr orImpl(Collection<Expr> pParams) {
    vectorExpr vExpr = new vectorExpr();
    for (Expr e : pParams) {
      vExpr.add(e);
    }
    return em.mkExpr(Kind.OR, vExpr);
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return em.mkExpr(Kind.XOR, pParam1, pParam2);
  }

  @Override
  protected Expr equivalence(Expr pBits1, Expr pBits2) {
    return em.mkExpr(Kind.IFF, pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Expr pBits) {
    return pBits.isConst() && pBits.getConstBoolean();
  }

  @Override
  protected boolean isFalse(Expr pBits) {
    return pBits.isConst() && !pBits.getConstBoolean();
  }

  @Override
  protected Expr ifThenElse(Expr pCond, Expr pF1, Expr pF2) {
    return pCond.iteExpr(pF1, pF2);
  }
}
