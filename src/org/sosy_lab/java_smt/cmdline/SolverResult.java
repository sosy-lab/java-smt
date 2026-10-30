/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.cmdline;

/** The result of a satisfiability check, as reported by the command-line interface. */
enum SolverResult {
  SAT("sat"),
  UNSAT("unsat"),
  UNKNOWN("unknown");

  private final String output;

  SolverResult(String pOutput) {
    output = pOutput;
  }

  /** The result as printed on stdout, i.e., in SMT-LIB2 notation. */
  @Override
  public String toString() {
    return output;
  }
}
