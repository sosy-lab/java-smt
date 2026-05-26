// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.theories.nia.GroebnerMultiplication;
import ap.types.Sort;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class PrincessIntegerFormulaManager
    extends PrincessNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  PrincessIntegerFormulaManager(
      PrincessFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected ITerm makeNumberImpl(long i) {
    return new IIntLit(IdealInt.apply(i));
  }

  @Override
  protected ITerm makeNumberImpl(BigInteger pI) {
    return new IIntLit(IdealInt.apply(pI.toString()));
  }

  @Override
  protected ITerm makeNumberImpl(String pI) {
    return new IIntLit(IdealInt.apply(pI));
  }

  @Override
  protected ITerm makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected IExpression makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  protected IExpression makeVariableImpl(String varName) {
    Sort t = getFormulaCreator().getIntegerType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  protected IExpression modularCongruence(
      IExpression pNumber1, IExpression pNumber2, long pModulo) {
    return modularCongruence0(pNumber1, pNumber2, makeNumberImpl(pModulo));
  }

  @Override
  protected IExpression modularCongruence(
      IExpression pNumber1, IExpression pNumber2, BigInteger pModulo) {
    return modularCongruence0(pNumber1, pNumber2, makeNumberImpl(pModulo));
  }

  private IExpression modularCongruence0(IExpression pNumber1, IExpression pNumber2, ITerm n) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    //    ITerm x = subtract(pNumber1, pNumber2);
    //    return x.$eq$eq$eq(n.$times(BitShiftMultiplication.eDiv(x, n)));
    //  exists v0. pNumber1 - pNumber2 + v0*n == 0
    ITerm diff = subtract(pNumber1, pNumber2);
    ITerm sum = add(diff, multiply(IExpression.v(0), n));
    return IExpression.ex(IExpression.eqZero(sum));
  }

  @Override
  public IExpression divide(IExpression pNumber1, IExpression pNumber2) {
    return GroebnerMultiplication.eDivWithSpecialZero((ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  public IExpression modulo(IExpression pNumber1, IExpression pNumber2) {
    return GroebnerMultiplication.eModWithSpecialZero((ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  public IExpression multiply(IExpression pNumber1, IExpression pNumber2) {
    return GroebnerMultiplication.mult((ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  protected boolean isNumeral(IExpression val) {
    return val instanceof IIntLit;
  }

  @Override
  protected IExpression floor(IExpression pNumber) {
    return pNumber; // identity for integers
  }

  @Override
  protected ITerm negate(IExpression pNumber) {
    return ((ITerm) pNumber).unary_$minus();
  }

  @Override
  protected ITerm add(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$plus((ITerm) pNumber2);
  }

  @Override
  protected ITerm subtract(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$minus((ITerm) pNumber2);
  }

  @Override
  protected IFormula greaterThan(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$greater((ITerm) pNumber2);
  }

  @Override
  protected IFormula greaterOrEquals(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$greater$eq((ITerm) pNumber2);
  }

  @Override
  protected IFormula lessThan(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$less((ITerm) pNumber2);
  }

  @Override
  protected IFormula lessOrEquals(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$less$eq((ITerm) pNumber2);
  }
}
