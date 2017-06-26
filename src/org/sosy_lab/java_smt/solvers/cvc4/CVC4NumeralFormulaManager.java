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
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

import java.math.BigInteger;

public abstract class CVC4NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Expr, Type, ExprManager, ParamFormulaType, ResultFormulaType, Expr> {

  protected final ExprManager exprManager;

  CVC4NumeralFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getExprManager();
  }

  abstract protected Type getNumeralType();

  @Override
  public boolean isNumeral(Expr pVal) {
    return pVal.getType().isInteger()
        || pVal.getType().isFloatingPoint()
        || pVal.getType().isReal(); // TODO is bitvector numeral?
  }

  @Override
  protected Expr makeNumberImpl(long i) {
    return exprManager.mkConst(new Rational(i));
  }

  @Override
  protected Expr makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected Expr makeNumberImpl(String pI) {
    return exprManager.mkConst(new Rational(pI));
  }

  @Override
  protected Expr makeVariableImpl(String varName) {
    Type type = getNumeralType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  public Expr divide(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.INTS_DIVISION, pParam1, pParam2);
  }

  @Override
  public Expr multiply(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.MULT, pParam1, pParam2);
  }

  @Override
  public Expr modulo(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.INTS_MODULUS, pParam1, pParam2);
  }

  @Override
  public Expr negate(Expr pParam1) {
    return exprManager.mkExpr(Kind.UMINUS, pParam1);
  }

  @Override
  public Expr add(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.PLUS, pParam1, pParam2);
  }

  @Override
  public Expr subtract(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.MINUS, pParam1, pParam2);
  }

  @Override
  public Expr equal(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  public Expr greaterThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.GT, pParam1, pParam2);
  }

  @Override
  public Expr greaterOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.GEQ, pParam1, pParam2);
  }

  @Override
  public Expr lessThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.LT, pParam1, pParam2);
  }

  @Override
  public Expr lessOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.LEQ, pParam1, pParam2);
  }
}
