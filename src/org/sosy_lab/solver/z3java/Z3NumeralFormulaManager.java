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

  static ArithExpr toAE(Expr e) {
    return (ArithExpr)e;
  }

  private static ArithExpr[] toAE(Collection<Expr> e) {
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
    return z3context.mkMul(minusOne, toAE(pNumber));
  }

  @Override
  public Expr add(Expr pNumber1, Expr pNumber2) {
    return z3context.mkAdd(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr sumImpl(List<Expr> operands) {
    return z3context.mkAdd(toAE(operands));
  }

  @Override
  public Expr subtract(Expr pNumber1, Expr pNumber2) {
    return z3context.mkSub(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr divide(Expr pNumber1, Expr pNumber2) {
    return z3context.mkDiv(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr multiply(Expr pNumber1, Expr pNumber2) {
    return z3context.mkMul(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, long pModulo) {
    return z3context.mkTrue();
  }

  @Override
  public Expr equal(Expr pNumber1, Expr pNumber2) {
    return z3context.mkEq(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr greaterThan(Expr pNumber1, Expr pNumber2) {
    return z3context.mkGt(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr greaterOrEquals(Expr pNumber1, Expr pNumber2) {
    return z3context.mkGe(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr lessThan(Expr pNumber1, Expr pNumber2) {
    return z3context.mkLt(toAE(pNumber1), toAE(pNumber2));
  }

  @Override
  public Expr lessOrEquals(Expr pNumber1, Expr pNumber2) {
    return z3context.mkLe(toAE(pNumber1), toAE(pNumber2));
  }
}
