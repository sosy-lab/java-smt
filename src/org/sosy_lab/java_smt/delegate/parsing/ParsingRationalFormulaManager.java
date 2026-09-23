/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class ParsingRationalFormulaManager
    extends ParsingNumeralFormulaManager<NumeralFormula, NumeralFormula.RationalFormula>
    implements RationalFormulaManager {
  ParsingRationalFormulaManager(
      RationalFormulaManager pDelegate, ParsingFormulaManager.Declarations pDeclarations) {
    super(pDelegate, pDeclarations);
  }
}
