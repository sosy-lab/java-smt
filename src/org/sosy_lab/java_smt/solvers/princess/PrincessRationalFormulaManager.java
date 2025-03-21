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
import ap.types.Sort;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
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
        case "int":
        case "Rat_int":
          assert fun.fun().arity() == 1;
          return ifmgr.isNumeral(fun.apply(0));
        case "frac":
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
    return divide(makeNumberImpl(pI.getNum()), makeNumberImpl(pI.getDen()));
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

  /** Make sure the value is real and add a cast if necessary */
  private ITerm toReal(ITerm number) {
    return formulaCreator.getFormulaType(number).isIntegerType()
        ? Rationals.int2ring(number)
        : number;
  }

  @Override
  protected IExpression floor(IExpression number) {
    throw new UnsupportedOperationException("floor is not supported in Princess");
  }

  @Override
  protected ITerm negate(IExpression number) {
    return Rationals.minus(toReal((ITerm) number));
  }

  @Override
  protected ITerm add(IExpression number1, IExpression number2) {
    return Rationals.plus(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IExpression sumImpl(List<IExpression> operands) {
    List<IExpression> castOperands =
        FluentIterable.from(operands).transform(t -> (IExpression) toReal((ITerm) t)).toList();
    return super.sumImpl(castOperands);
  }

  @Override
  protected ITerm subtract(IExpression number1, IExpression number2) {
    return Rationals.minus(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IExpression multiply(IExpression number1, IExpression number2) {
    return Rationals.mul(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IExpression divide(IExpression number1, IExpression number2) {
    return Rationals.div(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IFormula equal(IExpression number1, IExpression number2) {
    return super.equal(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IExpression distinctImpl(List<IExpression> operands) {
    List<IExpression> castOperands =
        FluentIterable.from(operands)
                .anyMatch(t -> Sort.sortOf((ITerm) t).equals(PrincessEnvironment.FRACTION_SORT))
            ? FluentIterable.from(operands).transform(t -> (IExpression) toReal((ITerm) t)).toList()
            : operands;
    return super.distinctImpl(castOperands);
  }

  @Override
  protected IFormula greaterThan(IExpression number1, IExpression number2) {
    return Rationals.gt(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IFormula greaterOrEquals(IExpression number1, IExpression number2) {
    return Rationals.geq(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IFormula lessThan(IExpression number1, IExpression number2) {
    return Rationals.lt(toReal((ITerm) number1), toReal((ITerm) number2));
  }

  @Override
  protected IFormula lessOrEquals(IExpression number1, IExpression number2) {
    return Rationals.leq(toReal((ITerm) number1), toReal((ITerm) number2));
  }
}
