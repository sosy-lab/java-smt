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

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import org.sosy_lab.solver.api.NumeralFormula;
import org.sosy_lab.solver.basicimpl.AbstractNumeralFormulaManager;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

abstract class Z3NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<Expr, Sort, Context, ParamFormulaType, ResultFormulaType> {

  protected final Context z3context;

  Z3NumeralFormulaManager(Z3FormulaCreator pCreator) {
    super(pCreator);
    this.z3context = pCreator.getEnv();
  }

  private static ArithExpr toNum(Expr e) {
    return (ArithExpr)e;
  }

  private static ArithExpr[] toNum(Collection<Expr> e) {
    return e.toArray(new ArithExpr[]{});
  }

  abstract protected Sort getNumeralType();

  @Override
  protected boolean isNumeral(Expr val) {
    return val.isNumeral();
  }

  @Override
  protected Expr makeNumberImpl(long i) {
    Sort sort = getNumeralType();
    return z3context.mkNumeral(i, sort);
  }

  @Override
  protected Expr makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected Expr makeNumberImpl(String pI) {
    Sort sort = getNumeralType();
    return z3context.mkNumeral(pI, sort);
  }

  @Override
  protected Expr makeVariableImpl(String varName) {
    Sort type = getNumeralType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  public Expr negate(Expr pNumber) {
    ArithExpr minusOne = z3context.mkInt(-1);
    return z3context.mkMul(minusOne, toNum(pNumber));
  }

  @Override
  public Expr add(Expr pNumber1, Expr pNumber2) {
    return z3context.mkAdd(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr sumImpl(List<Expr> operands) {
    return z3context.mkAdd(toNum(operands));
  }

  @Override
  public Expr subtract(Expr pNumber1, Expr pNumber2) {
    return z3context.mkSub(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr divide(Expr pNumber1, Expr pNumber2) {
    return z3context.mkDiv(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr multiply(Expr pNumber1, Expr pNumber2) {
    return z3context.mkMul(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, long pModulo) {
    return z3context.mkTrue();
  }

  @Override
  public Expr equal(Expr pNumber1, Expr pNumber2) {
    return z3context.mkEq(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr greaterThan(Expr pNumber1, Expr pNumber2) {
    return z3context.mkGt(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr greaterOrEquals(Expr pNumber1, Expr pNumber2) {
    return z3context.mkGe(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr lessThan(Expr pNumber1, Expr pNumber2) {
    return z3context.mkLt(toNum(pNumber1), toNum(pNumber2));
  }

  @Override
  public Expr lessOrEquals(Expr pNumber1, Expr pNumber2) {
    return z3context.mkLe(toNum(pNumber1), toNum(pNumber2));
  }
}
