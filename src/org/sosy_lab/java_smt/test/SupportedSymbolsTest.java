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
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.fail;

import com.google.common.collect.ImmutableList;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;

public class SupportedSymbolsTest extends ParameterizedSolverBasedTest0 {
  /** Valid symbol names. Taken from section 3.1 of the SMTLIB2 standard */
  private final List<String> goodSymbols =
      ImmutableList.of(
          "~!@$%^&*_-+=<>.?/",
          "x", "plus", "**", "$", "sas", "<adf", "abc77", "$s", "&6", ".", "kkk", ".8", "+34");

  /**
   * More valid symbol names from the SMTLIB standard. These names are already used for predefined
   * symbols and won't work with most solvers
   */
  private final List<String> badSymbols = ImmutableList.of("+", "<=", "<", ">", "*", "-32");

  /** Examples for invalid symbol names, also take from the SMTLIB standard */
  private final List<String> uglySymbols =
      ImmutableList.of(
          "_",
          "!",
          "as",
          "let",
          "exists",
          "forall",
          "match",
          "par",
          "",
          "assert",
          "check-sat",
          "check-sat-assuming",
          "declare-const",
          "declare-datatype",
          "declare-datatypes",
          "declare-fun",
          "declare-sort",
          "define-fun",
          "define-fun-rec",
          "define-funs-rec",
          "define-sort",
          "echo",
          "exit",
          "get-assertions",
          "get-assignment",
          "get-info",
          "get-model",
          "get-option",
          "get-proof",
          "get-unsat-assumptions",
          "get-unsat-core",
          "get-value",
          "pop",
          "push",
          "reset",
          "reset-assertions",
          "set-info",
          "set-logic",
          "set-option");

  /** Examples of valid quoted symbols. Taken from the SMTLIB standard */
  private final List<String> validQuoted =
      ImmutableList.of(
          "| this is a quoted symbol |",
          "| so is\nthis one |",
          "||",
          "| \" can occur too |",
          "| af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984|");

  /**
   * Examples of invalid quoted symbols
   *
   * <p>Only backslash and tilde are invalid inside a quoted symbol name
   */
  private final List<String> invalidQuoted = ImmutableList.of("|||", "|\\|");

  @Test
  public void goodSymbolTest() {
    // Works for all solvers!
    requireParser();
    for (String symbol : goodSymbols) {
      try {
        Formula f = mgr.parse("(declare-const " + symbol + " Bool) (assert " + symbol + ")");
        assertThat(f.toString()).isEqualTo(symbol);
      } catch (IllegalArgumentException ex) {
        fail("Failed on test input \"" + symbol + "\"");
      }
    }
  }

  @Test
  public void badSymbolTest() {
    // Only works with Bitwuzla
    // Z3 fails for "-32" and the rest for the other inputs
    requireParser();
    for (String symbol : badSymbols) {
      try {
        Formula f = mgr.parse("(declare-const " + symbol + " Bool) (assert " + symbol + ")");
        assertThat(f.toString()).isEqualTo(symbol);
      } catch (IllegalArgumentException ex) {
        fail("Failed on test input \"" + symbol + "\"");
      }
    }
  }

  @Test
  public void uglySymbolTest() {
    // Only works on Z3
    // Princess only throws an internal exception, but not "IllegalArgumentException"
    // The rest does not throw exceptions for all the reserved keywords
    requireParser();
    for (String symbol : uglySymbols) {
      assertThrows(
          "No IllegalArgumentException for \"" + symbol + "\"",
          IllegalArgumentException.class,
          () -> {
            Formula f = mgr.parse("(declare-const " + symbol + " Bool) (assert " + symbol + ")");
            assertThat(f.toString()).isEqualTo(symbol);
          });
    }
  }

  @Test
  public void validQuotedTest() {
    // Bitwuzla crashes for "| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ’]]984|"
    // MathSAT, SMTInterpol fail for "||"
    // Other solvers return the printed symbol without the quotes, even if that means that the
    // name is illegal.
    requireParser();
    for (String symbol : validQuoted) {
      try {
        Formula f = mgr.parse("(declare-const " + symbol + " Bool) (assert " + symbol + ")");
        assertThat(f.toString()).isEqualTo(symbol);
      } catch (IllegalArgumentException ex) {
        fail("Failed on test input \"" + symbol + "\"");
      }
    }
  }

  @Test
  public void invalidQuotedTest() {
    // Works for everything except Princess, which throws the wrong exception
    requireParser();
    for (String symbol : invalidQuoted) {
      assertThrows(
          IllegalArgumentException.class,
          () -> {
            Formula f = mgr.parse("(declare-const " + symbol + " Bool) (assert " + symbol + ")");
            assertThat(f.toString()).isEqualTo(symbol);
          });
    }
  }
}
