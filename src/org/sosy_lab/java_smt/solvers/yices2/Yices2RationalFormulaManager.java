/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  SPDX-License-Identifier: Apache-2.0 AND GPL-3.0-or-later
 */
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_division;

import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class Yices2RationalFormulaManager
    extends Yices2NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  protected Yices2RationalFormulaManager(
      Yices2FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected int getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Integer makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Integer makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  @Override
  public Integer divide(Integer pParam1, Integer pParam2) {
    if (isNumeral(pParam2)) {
      return yices_division(pParam1, pParam2);
    } else {
      return super.divide(pParam1, pParam2);
    }
  }
}
