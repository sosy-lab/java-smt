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
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
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
  protected IExpression makeNumberImpl(String i) {
    return makeNumberImpl(new BigDecimal(i));
  }

  @Override
  protected IExpression makeNumberImpl(double pNumber) {
    return makeNumberImpl(BigDecimal.valueOf(pNumber));
  }

  @Override
  protected IExpression makeNumberImpl(BigDecimal pNumber) {
    ArrayList<ITerm> args = new ArrayList<>(2);
    args.add(pInteger.makeNumberImpl(pNumber.unscaledValue()));
    args.add(pInteger.makeNumberImpl(BigInteger.valueOf(10).pow(pNumber.scale())));
    return new IFunApp(PrincessEnvironment.rationalTheory.frac(), PrincessEnvironment.toSeq(args));
  }

  @Override
  protected IExpression makeVariableImpl(String varName) {
    return getFormulaCreator().makeVariable(PrincessEnvironment.FRACTION_SORT, varName);
  }

  @Override
  protected IExpression floor(IExpression number) {
    throw new AssertionError("floor is not supported in Princess");
  }
}
