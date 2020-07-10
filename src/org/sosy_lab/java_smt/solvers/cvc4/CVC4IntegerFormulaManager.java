// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
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
