// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
final class BitwuzlaFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  BitwuzlaFormulaManager(
      BitwuzlaFormulaCreator pFormulaCreator,
      BitwuzlaUFManager pFunctionManager,
      BitwuzlaBooleanFormulaManager pBooleanManager,
      BitwuzlaBitvectorFormulaManager pBitvectorManager,
      BitwuzlaQuantifiedFormulaManager pQuantifierManager,
      BitwuzlaFloatingPointManager pFloatingPointManager,
      BitwuzlaArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        pFloatingPointManager,
        pQuantifierManager,
        pArrayManager,
        null,
        null,
        null);
  }

  /**
   * Parse a boolean formula given as a String in an SMTLIB file format. We expect exactly one
   * assertion to be contained in the query.
   *
   * <p>Example: <code>(declare-fun x () Int)(assert (= 0 x))</code>
   *
   * <p>It depends on the used SMT solver whether the given query must be self-contained and include
   * declarations for all used symbols or not, and also whether the query is allowed to contain
   * symbols with equal name, but different type/sort than existing symbols. The safest way is to
   * always declare all used symbols and to avoid conflicting types for them.
   *
   * <p>The behavior of the SMT solver is undefined if commands are provided in the SMTLIB-based
   * String that are different from declarations or an assertion, such as <code>push/pop</code> or
   * <code>set-info</code>. Most solvers just ignore those commands.
   *
   * <p>Variables that are defined, but not used in the assertion, might be ignored by the SMT
   * solver and they might not be available for later usage.
   *
   * @param s
   * @return A single formula from the assertion in the internal representation.
   * @throws IllegalArgumentException If the string cannot be parsed.
   */
  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    return null;
  }

  @Override
  public Appender dumpFormula(Long t) {
    return null;
  }

  static long getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }
}
