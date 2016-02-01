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

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;

import java.util.Collection;

class Z3BooleanFormulaManager extends AbstractBooleanFormulaManager<Expr, Sort, Context> {

  private final Context z3context;

  Z3BooleanFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    z3context = creator.getEnv();
  }

  private static BoolExpr toBool(Expr e) {
    return (BoolExpr)e;
  }

  static BoolExpr[] toBool(Collection<? extends Expr> e) {
    return e.toArray(new BoolExpr[]{});
  }

  @Override
  protected Expr makeVariableImpl(String varName) {
    Sort type = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Expr makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return z3context.mkTrue();
    } else {
      return z3context.mkFalse();
    }
  }

  @Override
  protected Expr not(Expr pParam) {
    return z3context.mkNot(toBool(pParam));
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    return z3context.mkAnd(toBool(pParam1), toBool(pParam2));
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    return z3context.mkOr(toBool(pParam1), toBool(pParam2));
  }

  @Override
  protected Expr orImpl(Collection<Expr> params) {
    return z3context.mkOr(toBool(params));
  }

  @Override
  protected Expr andImpl(Collection<Expr> params) {
    return z3context.mkAnd(toBool(params));
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return z3context.mkXor(toBool(pParam1), toBool(pParam2));
  }

  @Override
  protected Expr equivalence(Expr pBits1, Expr pBits2) {
    return z3context.mkEq(toBool(pBits1), toBool(pBits2));
  }

  @Override
  protected Expr implication(Expr pBits1, Expr pBits2) {
    return z3context.mkImplies(toBool(pBits1), toBool(pBits2));
  }

  @Override
  protected boolean isTrue(Expr pParam) {
    return toBool(pParam).isTrue();
  }

  @Override
  protected boolean isFalse(Expr pParam) {
    return toBool(pParam).isFalse();
  }

  @Override
  protected Expr ifThenElse(Expr pCond, Expr pF1, Expr pF2) {
    return z3context.mkITE(toBool(pCond), pF1, pF2);
  }
}
