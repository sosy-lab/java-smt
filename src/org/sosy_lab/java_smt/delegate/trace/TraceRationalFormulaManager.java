/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class TraceRationalFormulaManager
    extends TraceNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {
  final RationalFormulaManager delegate;
  final TraceLogger logger;

  TraceRationalFormulaManager(RationalFormulaManager pDelegate, TraceLogger pLogger) {
    super(pDelegate, pLogger);
    delegate = pDelegate;
    logger = pLogger;
  }
}
