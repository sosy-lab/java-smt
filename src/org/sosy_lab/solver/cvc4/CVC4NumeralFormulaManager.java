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

import org.sosy_lab.solver.api.NumeralFormula;
import org.sosy_lab.solver.basicimpl.AbstractNumeralFormulaManager;

public abstract class CVC4NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Expr, Type, CVC4Environment, ParamFormulaType, ResultFormulaType> {

  protected final ExprManager exprManager;

  protected CVC4NumeralFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = getFormulaCreator().getEnv().getExprManager();
  }

  @Override
  protected boolean isNumeral(Expr pVal) {
    return pVal.getType().isInteger()
        || pVal.getType().isFloatingPoint()
        || pVal.getType().isReal(); // TODO is bitvector numeral?
  }

  @Override
  protected Expr negate(Expr pParam1) {
    return exprManager.mkExpr(Kind.MINUS, pParam1);
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.PLUS, pParam1, pParam2);
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.MINUS, pParam1, pParam2);
  }

  @Override
  protected Expr equal(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.GT, pParam1, pParam2);
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.GEQ, pParam1, pParam2);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.LT, pParam1, pParam2);
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.LEQ, pParam1, pParam2);
  }
}
