/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class CVC4IntegerFormulaManager
    extends CVC4NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  CVC4IntegerFormulaManager(CVC4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Type getNumeralType() {
    return getFormulaCreator().getIntegerType();
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
  public Expr divide(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.INTS_DIVISION, pParam1, pParam2);
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, long pModulo) {
    return modularCongruence(pNumber1, pNumber2, BigInteger.valueOf(pModulo));
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, BigInteger pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    if (BigInteger.ZERO.compareTo(pModulo) < 0) {
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
    if (!INTEGER_NUMBER.matcher(pI).matches()) {
      throw new NumberFormatException("number is not an integer value: " + pI);
    }
    return super.makeNumberImpl(pI);
  }

  @Override
  protected Expr makeVariableImpl(String pI) {
    return formulaCreator.makeVariable(getFormulaCreator().getIntegerType(), pI);
  }
}
