// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

/**
 * Interface for operating over {@link RationalFormula}.
 *
 * <p>Rational formulas may take both integral and rational formulas as arguments.
 */
public interface RationalFormulaManager
    extends NumeralFormulaManager<NumeralFormula, RationalFormula> {

  @Override
  default FormulaType<RationalFormula> getFormulaType() {
    return FormulaType.RationalType;
  }
}
