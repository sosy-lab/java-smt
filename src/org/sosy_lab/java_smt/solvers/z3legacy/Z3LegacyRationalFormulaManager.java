/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import com.microsoft.z3legacy.Native;
import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

class Z3LegacyRationalFormulaManager
    extends Z3LegacyNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  Z3LegacyRationalFormulaManager(
      Z3LegacyFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected long getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  @Override
  protected Long toType(Long pNumber) {
    if (Native.getSort(z3context, pNumber) == formulaCreator.getIntegerType()) {
      long castedNumber = Native.mkInt2real(z3context, pNumber);
      Native.incRef(z3context, castedNumber);
      return castedNumber;
    } else {
      return pNumber;
    }
  }

  @Override
  protected Long floor(Long pNumber) {
    return Native.mkReal2int(z3context, pNumber);
  }
}
