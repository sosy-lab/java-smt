// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.utils;

import org.sosy_lab.java_smt.api.FormulaManager;

/** Central entry point for all utility classes. */
public final class SolverUtils {

  private SolverUtils() {}

  /**
   * Creates a new {@link UfElimination} instance.
   *
   * @param pFormulaManager the {@link FormulaManager} to be used
   * @return a new {@link UfElimination} instance
   */
  public static UfElimination ufElimination(FormulaManager pFormulaManager) {
    return new UfElimination(pFormulaManager);
  }

  /**
   * Creates a new {@link PrettyPrinter} instance.
   *
   * @param pFormulaManager the {@link FormulaManager} to be used
   * @return a new {@link PrettyPrinter} instance
   */
  public static PrettyPrinter prettyPrinter(FormulaManager pFormulaManager) {
    return new PrettyPrinter(pFormulaManager);
  }
}
