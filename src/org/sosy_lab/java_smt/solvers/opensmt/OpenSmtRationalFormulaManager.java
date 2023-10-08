// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;

public class OpenSmtRationalFormulaManager
    extends OpenSmtNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  OpenSmtRationalFormulaManager(
      OpenSmtFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected SRef getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected PTRef makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected PTRef makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  @Override
  public PTRef divide(PTRef pParam1, PTRef pParam2) {
    return osmtLogic.mkRealDiv(pParam1, pParam2);
  }

  @Override
  protected PTRef floor(PTRef pNumber) {
    throw new UnsupportedOperationException("OpenSMT does not support ´floor´ operation");
  }
}
