// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.solvers.opensmt.api.ArithLogic;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorPTRef;

@SuppressWarnings("ClassTypeParameterName")
abstract class OpenSmtNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        PTRef, SRef, Logic, ParamFormulaType, ResultFormulaType, SymRef> {

  protected final ArithLogic osmtLogic;

  OpenSmtNumeralFormulaManager(
      OpenSmtFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    osmtLogic = (ArithLogic) pCreator.getEnv();
  }

  protected abstract SRef getNumeralType();

  @Override
  protected boolean isNumeral(PTRef pVal) {
    return osmtLogic.isNumConst(pVal);
  }

  @Override
  protected PTRef makeNumberImpl(long i) {
    // we connot use "new Rational(long)", because it uses "unsigned long".
    return makeNumberImpl(Long.toString(i));
  }

  @Override
  protected PTRef makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected PTRef makeNumberImpl(String pI) {
    SRef type = getNumeralType();
    return osmtLogic.mkConst(type, pI);
  }

  @Override
  protected PTRef makeVariableImpl(String varName) {
    // FIXME: IllegalArgumentException should be thrown directly in the swig heade
    SRef type = getNumeralType();
    try {
      return getFormulaCreator().makeVariable(type, varName);
    } catch (RuntimeException e) {
      throw new IllegalArgumentException(e.getMessage());
    }
  }

  @Override
  protected PTRef multiply(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkTimes(pParam1, pParam2);
  }

  @Override
  protected PTRef modulo(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkMod(pParam1, pParam2);
  }

  @Override
  protected PTRef negate(PTRef pParam1) {
    return osmtLogic.mkNeg(pParam1);
  }

  @Override
  protected PTRef add(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkPlus(pParam1, pParam2);
  }

  @Override
  protected PTRef subtract(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkMinus(pParam1, pParam2);
  }

  @Override
  protected PTRef equal(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkEq(pParam1, pParam2);
  }

  @Override
  protected PTRef greaterThan(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkGt(pParam1, pParam2);
  }

  @Override
  protected PTRef greaterOrEquals(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkGeq(pParam1, pParam2);
  }

  @Override
  protected PTRef lessThan(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkLt(pParam1, pParam2);
  }

  @Override
  protected PTRef lessOrEquals(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkLeq(pParam1, pParam2);
  }

  @Override
  protected PTRef distinctImpl(List<PTRef> pParam) {
    return osmtLogic.mkDistinct(new VectorPTRef(pParam));
  }
}
