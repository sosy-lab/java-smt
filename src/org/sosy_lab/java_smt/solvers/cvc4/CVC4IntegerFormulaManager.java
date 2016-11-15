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
import edu.nyu.acsys.CVC4.Integer;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

public class CVC4IntegerFormulaManager
    extends CVC4NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  protected CVC4IntegerFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }

  @Override
  @SuppressWarnings("checkstyle:illegalinstantiation")
  public Expr makeNumberImpl(long pI) {
    if (pI < 0) {
      // TODO fix this bug
      return exprManager.mkConst(new Rational(new Integer((int) pI)));
    }
    return exprManager.mkConst(new Rational(new Integer(pI)));
  }

  @Override
  protected Expr makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Expr makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  protected Expr divide(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.INTS_DIVISION, pParam1, pParam2);
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.MULT, pParam1, pParam2);
  }

  @Override
  protected Expr modulo(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.INTS_MODULUS, pParam1, pParam2);
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, long pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    if (pModulo > 0) {
      Expr n = makeNumberImpl(pModulo);
      Expr x = subtract(pNumber1, pNumber2);
      return exprManager.mkExpr(
          Kind.EQUAL,
          x,
          exprManager.mkExpr(Kind.MULT, n, exprManager.mkExpr(Kind.INTS_DIVISION, x, n)));
    }
    return exprManager.mkConst(true);
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
  protected Expr makeVariableImpl(String pI) {
    return env.makeVariable(pI, getFormulaCreator().getIntegerType());
  }

  @Override
  public IntegerFormula makeNumber(long pNumber) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula makeNumber(BigInteger pNumber) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula makeNumber(double pNumber) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula makeNumber(BigDecimal pNumber) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula makeNumber(String pI) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula makeNumber(org.sosy_lab.common.rationals.Rational pRational) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula makeVariable(String pVar) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula negate(IntegerFormula pNumber) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula add(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula sum(List<IntegerFormula> pOperands) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula subtract(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula divide(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula modulo(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerFormula multiply(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula equal(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula greaterThan(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula greaterOrEquals(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula lessThan(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula lessOrEquals(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula pNumber1, IntegerFormula pNumber2,
      BigInteger pN) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula pNumber1, IntegerFormula pNumber2,
      long pN) {
    // TODO Auto-generated method stub
    return null;
  }
}
