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
package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

/**
 * Similar to the other Abstract*FormulaManager classes in this package,
 * this class serves as a helper for implementing {@link NumeralFormulaManager}.
 * It handles all the unwrapping and wrapping from {@link Formula}
 * instances to solver-specific formula representations,
 * such that the concrete class needs to handle only its own internal types.
 */
public abstract class AbstractNumeralFormulaManager<
        TFormulaInfo,
        TType,
        TEnv,
        ParamFormulaType extends NumeralFormula,
        ResultFormulaType extends NumeralFormula,
        TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {

  protected AbstractNumeralFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
  }

  protected ResultFormulaType wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulate(getFormulaType(), pTerm);
  }

  protected abstract boolean isNumeral(TFormulaInfo val);

  @Override
  public ResultFormulaType makeNumber(long i) {
    return wrap(makeNumberImpl(i));
  }

  protected abstract TFormulaInfo makeNumberImpl(long i);

  @Override
  public ResultFormulaType makeNumber(BigInteger i) {
    return wrap(makeNumberImpl(i));
  }

  protected abstract TFormulaInfo makeNumberImpl(BigInteger i);

  @Override
  public ResultFormulaType makeNumber(String i) {
    return wrap(makeNumberImpl(i));
  }

  protected abstract TFormulaInfo makeNumberImpl(String i);

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    return wrap(makeNumberImpl(pRational));
  }

  protected TFormulaInfo makeNumberImpl(Rational pRational) {
    return makeNumberImpl(pRational.toString());
  }

  @Override
  public ResultFormulaType makeNumber(double pNumber) {
    return wrap(makeNumberImpl(pNumber));
  }

  protected abstract TFormulaInfo makeNumberImpl(double pNumber);

  @Override
  public ResultFormulaType makeNumber(BigDecimal pNumber) {
    return wrap(makeNumberImpl(pNumber));
  }

  protected abstract TFormulaInfo makeNumberImpl(BigDecimal pNumber);

  /**
   * This method tries to represent a BigDecimal using only BigInteger.
   * It can be used for implementing {@link #makeNumber(BigDecimal)}
   * when the current theory supports only integers and division by constants.
   */
  protected final TFormulaInfo decimalAsInteger(BigDecimal val) {
    if (val.scale() <= 0) {
      // actually an integral number
      return makeNumberImpl(convertBigDecimalToBigInteger(val));

    } else {
      // represent x.y by xy / (10^z) where z is the number of digits in y
      // (the "scale" of a BigDecimal)

      BigDecimal n = val.movePointRight(val.scale()); // this is "xy"
      BigInteger numerator = convertBigDecimalToBigInteger(n);

      BigDecimal d = BigDecimal.ONE.scaleByPowerOfTen(val.scale()); // this is "10^z"
      BigInteger denominator = convertBigDecimalToBigInteger(d);
      assert denominator.signum() > 0;

      return divide(makeNumberImpl(numerator), makeNumberImpl(denominator));
    }
  }

  private static BigInteger convertBigDecimalToBigInteger(BigDecimal d)
      throws NumberFormatException {
    try {
      return d.toBigIntegerExact();
    } catch (ArithmeticException e) {
      NumberFormatException nfe =
          new NumberFormatException("Cannot represent BigDecimal " + d + " as BigInteger");
      nfe.initCause(e);
      throw nfe;
    }
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    checkVariableName(pVar);
    return wrap(makeVariableImpl(pVar));
  }

  protected abstract TFormulaInfo makeVariableImpl(String i);

  @Override
  public ResultFormulaType negate(ParamFormulaType pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrap(negate(param1));
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public ResultFormulaType add(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(add(param1, param2));
  }

  protected abstract TFormulaInfo add(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    return wrap(sumImpl(Lists.transform(operands, this::extractInfo)));
  }

  protected TFormulaInfo sumImpl(List<TFormulaInfo> operands) {
    TFormulaInfo result = makeNumberImpl(0);
    for (TFormulaInfo operand : operands) {
      result = add(result, operand);
    }
    return result;
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(subtract(param1, param2));
  }

  protected abstract TFormulaInfo subtract(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public ResultFormulaType divide(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    return wrap(divide(param1, param2));
  }

  /**
   * If a solver does not support this operation, e.g. because of missing
   * support for non-linear arithmetics, we throw UnsupportedOperationException.
   *
   * @param pParam1 the dividend
   * @param pParam2 the divisor
   */
  protected TFormulaInfo divide(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public ResultFormulaType modulo(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    return wrap(modulo(param1, param2));
  }

  /**
   * If a solver does not support this operation, e.g. because of missing
   * support for non-linear arithmetics, we throw UnsupportedOperationException.
   *
   * @param pParam1 the dividend
   * @param pParam2 the divisor
   */
  protected TFormulaInfo modulo(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    throw new UnsupportedOperationException();
  }

  public BooleanFormula modularCongruence(
      ParamFormulaType pNumber1, ParamFormulaType pNumber2, long pModulo) {
    Preconditions.checkArgument(pModulo > 0, "modular congruence needs a positive modulo.");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(modularCongruence(param1, param2, pModulo));
  }

  public BooleanFormula modularCongruence(
      ParamFormulaType pNumber1, ParamFormulaType pNumber2, BigInteger pModulo) {
    Preconditions.checkArgument(pModulo.signum() > 0, "modular congruence needs a positive modulo.");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(modularCongruence(param1, param2, pModulo));
  }

  protected TFormulaInfo modularCongruence(TFormulaInfo a, TFormulaInfo b, BigInteger m) {
    throw new UnsupportedOperationException();
  }

  /**
   * If a solver does not support this operation, e.g. because of missing
   * support for linear arithmetic division, we throw UnsupportedOperationException.
   *
   * @param a first operand
   * @param b second operand
   * @param m the modulus
   * @return the formula representing "(a % m) == (b % m)"
   */
  protected TFormulaInfo modularCongruence(TFormulaInfo a, TFormulaInfo b, long m) {
    throw new UnsupportedOperationException();
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    return wrap(multiply(param1, param2));
  }

  /**
   * If a solver does not support this operation, e.g. because of missing
   * support for non-linear arithmetics, we throw UnsupportedOperationException.
   *
   * @param pParam1 first factor
   * @param pParam2 second factor
   */
  protected TFormulaInfo multiply(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula equal(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(equal(param1, param2));
  }

  protected abstract TFormulaInfo equal(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessThan(param1, param2));
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);
}
