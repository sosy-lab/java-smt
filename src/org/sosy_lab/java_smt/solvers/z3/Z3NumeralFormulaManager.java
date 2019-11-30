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
package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

abstract class Z3NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Long, Long, Long, ParamFormulaType, ResultFormulaType, Long> {

  protected final long z3context;

  Z3NumeralFormulaManager(Z3FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    this.z3context = pCreator.getEnv();
  }

  protected abstract long getNumeralType();

  @Override
  protected boolean isNumeral(Long val) {
    return Native.isNumeralAst(z3context, val);
  }

  @Override
  protected Long makeNumberImpl(long i) {
    long sort = getNumeralType();
    return Native.mkInt64(z3context, i, sort);
  }

  @Override
  protected Long makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected Long makeNumberImpl(String pI) {
    long sort = getNumeralType();
    return Native.mkNumeral(z3context, pI, sort);
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getNumeralType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long negate(Long pNumber) {
    long sort = Native.getSort(z3context, pNumber);
    long minusOne = Native.mkInt(z3context, -1, sort);
    return Native.mkMul(z3context, 2, new long[] {minusOne, pNumber});
  }

  @Override
  protected Long add(Long pNumber1, Long pNumber2) {
    return Native.mkAdd(z3context, 2, new long[] {pNumber1, pNumber2});
  }

  @Override
  protected Long sumImpl(List<Long> operands) {
    return Native.mkAdd(z3context, operands.size(), Longs.toArray(operands));
  }

  @Override
  protected Long subtract(Long pNumber1, Long pNumber2) {
    return Native.mkSub(z3context, 2, new long[] {pNumber1, pNumber2});
  }

  @Override
  protected Long divide(Long pNumber1, Long pNumber2) {
    return Native.mkDiv(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long multiply(Long pNumber1, Long pNumber2) {
    return Native.mkMul(z3context, 2, new long[] {pNumber1, pNumber2});
  }

  @Override
  protected Long equal(Long pNumber1, Long pNumber2) {
    return Native.mkEq(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long distinctImpl(List<Long> pNumbers) {
    return Native.mkDistinct(z3context, pNumbers.size(), Longs.toArray(pNumbers));
  }

  @Override
  protected Long greaterThan(Long pNumber1, Long pNumber2) {
    return Native.mkGt(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long greaterOrEquals(Long pNumber1, Long pNumber2) {
    return Native.mkGe(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long lessThan(Long pNumber1, Long pNumber2) {
    return Native.mkLt(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long lessOrEquals(Long pNumber1, Long pNumber2) {
    return Native.mkLe(z3context, pNumber1, pNumber2);
  }
}
