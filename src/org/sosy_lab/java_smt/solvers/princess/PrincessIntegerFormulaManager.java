/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.princess;

import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.theories.BitShiftMultiplication;

import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

import java.math.BigDecimal;
import java.math.BigInteger;

class PrincessIntegerFormulaManager
    extends PrincessNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  PrincessIntegerFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
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
    PrincessTermType t = getFormulaCreator().getIntegerType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  protected IExpression modularCongruence(
      IExpression pNumber1, IExpression pNumber2, long pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    ITerm n = makeNumberImpl(pModulo);
    ITerm x = subtract(pNumber1, pNumber2);
    return x.$eq$eq$eq(n.$times(BitShiftMultiplication.eDiv(x, n)));
  }

  @Override
  public IExpression divide(IExpression pNumber1, IExpression pNumber2) {
    return BitShiftMultiplication.eDiv((ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  public IExpression modulo(IExpression pNumber1, IExpression pNumber2) {
    return BitShiftMultiplication.eMod((ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  public IExpression multiply(IExpression pNumber1, IExpression pNumber2) {
    IExpression result;
    try {
      result = ((ITerm) pNumber1).$times((ITerm) pNumber2);
    } catch (IllegalArgumentException e) {
      result = BitShiftMultiplication.mult((ITerm) pNumber1, (ITerm) pNumber2);
    }
    return result;
  }

  @Override
  protected boolean isNumeral(IExpression val) {
    return val instanceof IIntLit;
  }
}
