// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.math.BigDecimal;
import java.math.BigInteger;
import opensmt.PTRef;
import opensmt.SRef;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class OpenSmtIntegerFormulaManager
    extends OpenSmtNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  OpenSmtIntegerFormulaManager(
      OpenSmtFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected SRef getNumeralType() {
    return getFormulaCreator().getIntegerType();
  }

  @Override
  protected PTRef makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected PTRef makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  protected PTRef divide(PTRef pParam1, PTRef pParam2) {
    return logic.mkIntDiv(pParam1, pParam2);
  }

  @Override
  protected PTRef modularCongruence(PTRef pNumber1, PTRef pNumber2, long pModulo) {
    return modularCongruence(pNumber1, pNumber2, BigInteger.valueOf(pModulo));
  }

  @Override
  protected PTRef modularCongruence(PTRef pNumber1, PTRef pNumber2, BigInteger pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    if (BigInteger.ZERO.compareTo(pModulo) < 0) {
      PTRef n = makeNumberImpl(pModulo);
      PTRef x = subtract(pNumber1, pNumber2);
      return logic.mkEq(x, logic.mkTimes(n, logic.mkIntDiv(x, n)));
    }
    return logic.getTerm_true();
  }
}
