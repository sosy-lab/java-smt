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
import edu.nyu.acsys.CVC4.Integer;
import edu.nyu.acsys.CVC4.Rational;

import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;

import java.math.BigDecimal;
import java.math.BigInteger;

public class CVC4IntegerFormulaManager
    extends CVC4NumeralFormulaManager<IntegerFormula, IntegerFormula> {

  protected CVC4IntegerFormulaManager(
      CVC4FormulaCreator pCreator,
      CVC4FunctionFormulaManager pFunctionManager,
      boolean pUseNonLinearArithmetic) {
    super(pCreator, pFunctionManager, pUseNonLinearArithmetic);
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }


  @Override
  @SuppressWarnings("checkstyle:IllegalInstantiation")
  public Expr makeNumberImpl(long pI) {
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
  public Expr linearDivide(Expr pNumber1, Expr pNumber2) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, long pModulo) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected Expr makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.longValue());
  }

  @Override
  protected Expr makeNumberImpl(String pI) {
    return makeNumberImpl(Long.parseLong(pI));
  }

  @Override
  protected Expr makeVariableImpl(String pI) {
    return exprManager.mkVar(pI, getFormulaCreator().getIntegerType());
  }
}
