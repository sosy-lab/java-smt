// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.ITerm;
import ap.theories.rationals.Rationals;
import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.function.BiFunction;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class PrincessRationalFormulaManager
    extends PrincessNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  private PrincessIntegerFormulaManager ifmgr;

  PrincessRationalFormulaManager(
      PrincessFormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic,
      PrincessIntegerFormulaManager pIntegerFormulaManager) {
    super(pCreator, pNonLinearArithmetic);
    this.ifmgr = pIntegerFormulaManager;
  }

  @Override
  protected boolean isNumeral(IExpression value) {
    if (value instanceof IFunApp) {
      IFunApp fun = (IFunApp) value;
      switch (fun.fun().name()) {
        case "Rat_fromRing":
          assert fun.fun().arity() == 1;
          return ifmgr.isNumeral(fun.apply(0));
        case "Rat_frac":
          assert fun.fun().arity() == 2;
          return ifmgr.isNumeral(fun.apply(0)) && ifmgr.isNumeral(fun.apply(1));
      }
    }
    return false;
  }

  protected IExpression fromInteger(ITerm i) {
    return PrincessEnvironment.rationalTheory.int2ring(i);
  }

  @Override
  protected IExpression makeNumberImpl(long i) {
    return fromInteger(ifmgr.makeNumberImpl(i));
  }

  @Override
  protected IExpression makeNumberImpl(BigInteger i) {
    return fromInteger(ifmgr.makeNumberImpl(i));
  }

  @Override
  protected IExpression makeNumberImpl(Rational pI) {
    return new IFunApp(
        Rationals.frac(),
        PrincessEnvironment.toITermSeq(
            ifmgr.makeNumberImpl(pI.getNum()), ifmgr.makeNumberImpl(pI.getDen())));
  }

  @Override
  protected IExpression makeNumberImpl(String i) {
    return makeNumberImpl(new BigDecimal(i));
  }

  @Override
  protected IExpression makeNumberImpl(double pNumber) {
    return makeNumberImpl(BigDecimal.valueOf(pNumber));
  }

  @Override
  protected IExpression makeNumberImpl(BigDecimal pNumber) {
    if (pNumber.stripTrailingZeros().scale() <= 0) {
      // We have an integer number
      // Return the term for a/1
      return PrincessEnvironment.rationalTheory.int2ring(
          ifmgr.makeNumberImpl(pNumber.toBigInteger()));
    } else {
      // We have a fraction a/b
      // Convert the numerator and the divisor and then return the fraction
      List<ITerm> args =
          ImmutableList.of(
              ifmgr.makeNumberImpl(pNumber.unscaledValue()),
              ifmgr.makeNumberImpl(BigInteger.valueOf(10).pow(pNumber.scale())));
      return new IFunApp(
          PrincessEnvironment.rationalTheory.frac(), PrincessEnvironment.toSeq(args));
    }
  }

  @Override
  protected IExpression makeVariableImpl(String varName) {
    return getFormulaCreator().makeVariable(PrincessEnvironment.FRACTION_SORT, varName);
  }

  @Override
  protected IExpression floor(IExpression number) {
    throw new UnsupportedOperationException("floor is not supported in Princess");
  }

  @Override
  protected ITerm negate(IExpression pNumber) {
    return Rationals.minus((ITerm) pNumber);
  }

  /** Cast both arguments to <code>rational</code> and apply the operation */
  private <RType> RType applyWithCast(BiFunction<ITerm, ITerm, RType> op, ITerm arg1, ITerm arg2) {
    FormulaType<?> sort1 = getFormulaCreator().getFormulaType(arg1);
    FormulaType<?> sort2 = getFormulaCreator().getFormulaType(arg2);

    ITerm castArg1 = sort1.isIntegerType() ? Rationals.int2ring(arg1) : arg1;
    ITerm castArg2 = sort2.isIntegerType() ? Rationals.int2ring(arg2) : arg2;

    return op.apply(castArg1, castArg2);
  }

  @Override
  protected ITerm add(IExpression pNumber1, IExpression pNumber2) {
    return applyWithCast(Rationals::plus, (ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  protected ITerm subtract(IExpression pNumber1, IExpression pNumber2) {
    return applyWithCast(Rationals::minus, (ITerm) pNumber1, (ITerm) pNumber2);
  }

  @Override
  protected IExpression multiply(IExpression number1, IExpression number2) {
    return applyWithCast(Rationals::mul, (ITerm) number1, (ITerm) number2);
  }

  @Override
  protected IExpression divide(IExpression number1, IExpression number2) {
    return applyWithCast(Rationals::div, (ITerm) number1, (ITerm) number2);
  }

  @Override
  protected IFormula greaterThan(IExpression number1, IExpression number2) {
    return applyWithCast(Rationals::gt, (ITerm) number1, (ITerm) number2);
  }

  @Override
  protected IFormula greaterOrEquals(IExpression number1, IExpression number2) {
    return applyWithCast(Rationals::geq, (ITerm) number1, (ITerm) number2);
  }

  @Override
  protected IFormula lessThan(IExpression number1, IExpression number2) {
    return applyWithCast(Rationals::lt, (ITerm) number1, (ITerm) number2);
  }

  @Override
  protected IFormula lessOrEquals(IExpression number1, IExpression number2) {
    return applyWithCast(Rationals::leq, (ITerm) number1, (ITerm) number2);
  }
}
