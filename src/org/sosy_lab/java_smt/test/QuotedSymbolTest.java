/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;

public class QuotedSymbolTest extends ParameterizedSolverBasedTest0 {

  // TODO Try the same tests for UFs
  // TODO See what happens when the quotes are not needed. Does parsing/printing still preserve
  //  them?
  // TODO Try the tests on some larger formulas

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void quotedSymbolTest() {
    // Test if quoted strings are accepted as variable names
    bmgr.makeVariable("|exit|");
  }

  @Test
  public void quotedVisitorTest() {
    // Test visitor for quoted symbols
    assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);

    BooleanFormula f = bmgr.makeVariable("|exit|");
    var symbols = mgr.extractVariables(f);

    assertThat(symbols.keySet()).containsExactly("|exit|");
    assertThat(symbols.values().stream().map(Formula::toString)).containsExactly("|exit|");
  }

  @Test
  public void quotedPrintingTest() {
    // TODO CVC4 adds weird underscores when using quoted symbols. For example |,| becomes |_,_|.
    //  Find a way to remove them.

    // Test printing for quoted symbols
    BooleanFormula f = bmgr.makeVariable("|exit|");
    String smtlib = mgr.dumpFormula(f).toString();

    String expected;
    switch (solverToUse()) {
      case BITWUZLA:
        expected = "(declare-const |exit| Bool)";
        break;
      case BOOLECTOR:
        expected = "(declare-fun |exit| () (_ BitVec 1))";
        break;
      default:
        expected = "(declare-fun |exit| () Bool)";
    }
    assertThat(smtlib).startsWith(expected);
  }

  @Test
  public void quotedParseTest() {
    // Test if quoted symbols are kept in quotes while parsing
    requireParser();

    BooleanFormula f = mgr.parse("(declare-fun |exit| () Bool) (assert |exit|)");
    assertThat(f.toString()).isEqualTo("|exit|");
  }
}
