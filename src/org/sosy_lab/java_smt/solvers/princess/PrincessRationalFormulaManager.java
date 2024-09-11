// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.parser.IFunApp;
import ap.parser.ITerm;
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

  private PrincessIntegerFormulaManager pInteger;

  PrincessRationalFormulaManager(
      PrincessFormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic,
      PrincessIntegerFormulaManager pInteger) {
    super(pCreator, pNonLinearArithmetic);
    this.pInteger = pInteger;
  }

  @Override
  protected boolean isNumeral(IExpression value) {
    if (value instanceof IFunApp) {
      IFunApp fun = (IFunApp) value;
      switch (fun.fun().name()) {
        case "int":
        case "Rat_int":
          assert fun.fun().arity() == 1;
          return pInteger.isNumeral(fun.apply(0));
        case "frac":
          assert fun.fun().arity() == 2;
          return pInteger.isNumeral(fun.apply(0)) && pInteger.isNumeral(fun.apply(1));
      }
    }
    return false;
  }

  protected IExpression fromInteger(ITerm i) {
    return PrincessEnvironment.rationalTheory.int2ring(i);
  }

  @Override
  protected IExpression makeNumberImpl(long i) {
    return fromInteger(pInteger.makeNumberImpl(i));
  }

  @Override
  protected IExpression makeNumberImpl(BigInteger i) {
    return fromInteger(pInteger.makeNumberImpl(i));
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
    if (pNumber.scale() <= 0) {
      return PrincessEnvironment.rationalTheory.int2ring(
          pInteger.makeNumberImpl(pNumber.toBigInteger()));
    } else {
      List<ITerm> args =
          ImmutableList.of(
              pInteger.makeNumberImpl(pNumber.unscaledValue()),
              pInteger.makeNumberImpl(BigInteger.valueOf(10).pow(pNumber.scale())));
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
    throw new AssertionError("floor is not supported in Princess");
  }

  @Override
  protected IExpression multiply(IExpression number1, IExpression number2) {
    return PrincessEnvironment.rationalTheory.mul((ITerm) number1, (ITerm) number2);
  }

  @Override
  protected IExpression divide(IExpression number1, IExpression number2) {
    return PrincessEnvironment.rationalTheory.div((ITerm) number1, (ITerm) number2);
  }
}
