// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import com.google.common.primitives.Ints;
import com.sri.yices.Constructor;
import com.sri.yices.Terms;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class Yices2NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Integer, Integer, Long, ParamFormulaType, ResultFormulaType, Integer> {

  private final boolean supportsNonLinearArithmetic;

  Yices2NumeralFormulaManager(
      Yices2FormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic,
      boolean pSupportsNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    supportsNonLinearArithmetic = pSupportsNonLinearArithmetic;
  }

  /**
   * DPLL(T) only supports linear arithmetic, but Yices2 reports a non-linear term only when it is
   * asserted. We already reject non-linear terms when creating them, so that the option
   * solver.nonLinearArithmetic=APPROXIMATE_FALLBACK can replace them with an UF.
   */
  protected void checkNonLinearArithmeticIsSupported() {
    if (!supportsNonLinearArithmetic) {
      throw new UnsupportedOperationException(
          "Non-linear arithmetic is not supported in the current logic, as Yices2 uses DPLL(T)"
              + " for it. Set solver.yices2.logic to a non-linear logic like QF_NIA, or"
              + " approximate non-linear arithmetic with"
              + " solver.nonLinearArithmetic=APPROXIMATE_FALLBACK.");
    }
  }

  @Override
  protected boolean isNumeral(Integer pVal) {
    return Terms.constructor(pVal) == Constructor.ARITH_CONSTANT;
  }

  @Override
  public Integer makeNumberImpl(long pI) {
    return Terms.intConst(pI);
  }

  @Override
  public Integer makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  public Integer makeNumberImpl(String pI) {
    if (pI.contains("/")) {
      return Terms.parseRational(pI);
    } else {
      return Terms.parseFloat(pI);
    }
  }

  protected abstract int getNumeralType();

  @Override
  public Integer makeVariableImpl(String pI) {
    return getFormulaCreator().makeVariable(getNumeralType(), pI);
  }

  @Override
  public Integer negate(Integer pParam1) {
    return Terms.neg(pParam1);
  }

  @Override
  public Integer add(Integer pParam1, Integer pParam2) {
    return Terms.add(pParam1, pParam2);
  }

  @Override
  public Integer subtract(Integer pParam1, Integer pParam2) {
    return Terms.sub(pParam1, pParam2);
  }

  @Override
  public Integer multiply(Integer pParam1, Integer pParam2) {
    if (!isNumeral(pParam1) && !isNumeral(pParam2)) {
      checkNonLinearArithmeticIsSupported();
    }
    return Terms.mul(pParam1, pParam2);
  }

  @Override
  public Integer equal(Integer pParam1, Integer pParam2) {
    return Terms.arithEq(pParam1, pParam2);
  }

  @Override
  public Integer distinctImpl(List<Integer> pNumbers) {
    if (pNumbers.size() < 2) {
      return Terms.mkTrue();
    } else {
      return Terms.distinct(Ints.toArray(pNumbers));
    }
  }

  @Override
  public Integer greaterThan(Integer pParam1, Integer pParam2) {
    return Terms.arithGt(pParam1, pParam2);
  }

  @Override
  public Integer greaterOrEquals(Integer pParam1, Integer pParam2) {
    return Terms.arithGeq(pParam1, pParam2);
  }

  @Override
  public Integer lessThan(Integer pParam1, Integer pParam2) {
    return Terms.arithLt(pParam1, pParam2);
  }

  @Override
  public Integer lessOrEquals(Integer pParam1, Integer pParam2) {
    return Terms.arithLeq(pParam1, pParam2);
  }

  @Override
  protected Integer floor(Integer pNumber) {
    return Terms.floor(pNumber);
  }
}
