// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

final class LeanSmtRationalFormulaManager
    extends LeanSmtNumeralFormulaManager<NumeralFormula, NumeralFormula.RationalFormula>
    implements RationalFormulaManager {

  LeanSmtRationalFormulaManager(
      LeanSmtFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected LeanSmtType getNumeralType() {
    return LeanSmtType.REAL;
  }

  @Override
  protected FormulaType<?> getNumericFormulaType() {
    return FormulaType.RationalType;
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }
}

