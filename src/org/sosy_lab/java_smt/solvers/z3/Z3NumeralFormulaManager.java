// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
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
    if (operands.isEmpty()) {
      return makeNumberImpl(0);
    } else {
      return Native.mkAdd(z3context, operands.size(), Longs.toArray(operands));
    }
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
