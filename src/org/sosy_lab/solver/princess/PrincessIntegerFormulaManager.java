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
package org.sosy_lab.solver.princess;

import static org.sosy_lab.solver.princess.PrincessUtil.castToTerm;
import static org.sosy_lab.solver.princess.PrincessUtil.isNumber;

import ap.basetypes.IdealInt;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.theories.BitShiftMultiplication;

import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;

import java.math.BigDecimal;
import java.math.BigInteger;

class PrincessIntegerFormulaManager
    extends org.sosy_lab.solver.princess.PrincessNumeralFormulaManager<
        IntegerFormula, IntegerFormula> {

  PrincessIntegerFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
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
    TermType t = getFormulaCreator().getIntegerType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  protected IExpression modularCongruence(
      IExpression pNumber1, IExpression pNumber2, long pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    if (pModulo > 0) {
      ITerm n = makeNumberImpl(pModulo);
      ITerm x = subtract(pNumber1, pNumber2);
      return x.$eq$eq$eq(n.$times(BitShiftMultiplication.eDiv(x, n)));
    }
    return new IBoolLit(true);
  }

  @Override
  public IExpression divide(IExpression pNumber1, IExpression pNumber2) {
    return BitShiftMultiplication.eDiv(castToTerm(pNumber1), castToTerm(pNumber2));
  }

  @Override
  public IExpression modulo(IExpression pNumber1, IExpression pNumber2) {
    return BitShiftMultiplication.eMod(castToTerm(pNumber1), castToTerm(pNumber2));
  }

  @Override
  public IExpression multiply(IExpression pNumber1, IExpression pNumber2) {
    return castToTerm(pNumber1).$times(castToTerm(pNumber2));
  }

  @Override
  protected boolean isNumeral(IExpression val) {
    return isNumber(val);
  }
}
