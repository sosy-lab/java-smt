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
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

public class CVC4BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Expr, Type, CVC4Environment> {

  private final ExprManager exprManager;
  private final CVC4FormulaCreator creator;
  private final CVC4UnsafeFormulaManager ufmgr;

  protected CVC4BooleanFormulaManager(CVC4FormulaCreator pCreator, CVC4UnsafeFormulaManager ufmgr) {
    super(pCreator, ufmgr);
    exprManager = pCreator.getEnv().getExprManager();
    this.ufmgr = ufmgr;
    this.creator = pCreator;
  }

  @Override
  protected Expr makeVariableImpl(String pVar) {
    return exprManager.mkVar(pVar, getFormulaCreator().getBoolType());
  }

  @Override
  protected Expr makeBooleanImpl(boolean pValue) {
    return exprManager.mkConst(pValue);
  }

  @Override
  protected Expr not(Expr pParam1) {
    return exprManager.mkExpr(Kind.NOT, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.OR, pParam1, pParam2);
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.XOR, pParam1, pParam2);
  }

  @Override
  protected boolean isNot(Expr pParam) {
    return pParam.getKind() == Kind.NOT;
  }

  @Override
  protected boolean isAnd(Expr pParam) {
    return pParam.getKind() == Kind.AND;
  }

  @Override
  protected boolean isOr(Expr pParam) {
    return pParam.getKind() == Kind.OR;
  }

  @Override
  protected boolean isXor(Expr pParam) {
    return pParam.getKind() == Kind.XOR;
  }

  @Override
  protected Expr equivalence(Expr pBits1, Expr pBits2) {
    return exprManager.mkExpr(Kind.EQUAL, pBits1, pBits2);
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

  @Override
  protected boolean isEquivalence(Expr pBits) {
    // TODO is there a relevant difference that needs to be handled here?
    return pBits.getKind() == Kind.EQUAL || pBits.getKind() == Kind.IFF;
  }

  @Override
  protected boolean isImplication(Expr pFormula) {
    return pFormula.getKind() == Kind.IMPLIES;
  }

  @Override
  protected boolean isIfThenElse(Expr pBits) {
    return pBits.getKind() == Kind.ITE;
  }

  private boolean isAtom(Expr pF) {
    return pF.isConst() || pF.isVariable(); // TODO is this correct?
  }

  @Override
  protected <R> R visit(BooleanFormulaVisitor<R> pVisitor, Expr f) {
    if (isTrue(f)) {
      assert ufmgr.getArity(f) == 0;
      return pVisitor.visitTrue();
    } else if (isFalse(f)) {
      assert ufmgr.getArity(f) == 0;
      return pVisitor.visitFalse();
    } else if (isNot(f)) {
      assert ufmgr.getArity(f) == 1;
      return pVisitor.visitNot(getArg(f, 0));
    } else if (isAnd(f)) {
      if (ufmgr.getArity(f) == 0) {
        return pVisitor.visitTrue();
      } else if (ufmgr.getArity(f) == 1) {
        return visit(pVisitor, ufmgr.getArg(f, 0));
      }
      return pVisitor.visitAnd(getAllArgs(f));
    } else if (isOr(f)) {
      if (ufmgr.getArity(f) == 0) {
        return pVisitor.visitFalse();
      } else if (ufmgr.getArity(f) == 1) {
        return pVisitor.visit(getArg(f, 0));
      }
      return pVisitor.visitOr(getAllArgs(f));
    } else if (isEquivalence(f)) {
      assert ufmgr.getArity(f) == 2;
      return pVisitor.visitEquivalence(getArg(f, 0), getArg(f, 1));
    } else if (isIfThenElse(f)) {
      assert ufmgr.getArity(f) == 3;
      return pVisitor.visitIfThenElse(getArg(f, 0), getArg(f, 1), getArg(f, 2));
    } else if (isAtom(f)) {
      return pVisitor.visitAtom(getFormulaCreator().encapsulateBoolean(f));
    }
    throw new UnsupportedOperationException("Unknown or unsupported boolean operator " + f);
  }
}
