/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.truth.Truth.assertThat;

import org.junit.Test;

public class TokenizerTest {
  @Test
  public void validBrackets() {
    String smtlib = "(assert (= 3 (+ 2 1)))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test(expected = IllegalArgumentException.class)
  public void invalidClose() {
    String smtlib = "(assert (= 3 (+ 2 1))))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test(expected = IllegalArgumentException.class)
  public void invalidOpen() {
    String smtlib = "(assert (= 3 (+ 2 1))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void parenthesesInComment() {
    String smtlib = "(assert (= 3;)\n(- 4 1)))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly("(assert (= 3 (- 4 1)))");
  }

  @Test
  public void parenthesesInString() {
    String smtlib = "(assert (= v \")\"))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void parenthesesInQuotedSymbol() {
    String smtlib = "(assert (= |)v| 0))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void splitCommands() {
    String part1 = "(define-const v Int)";
    String part2 = "(assert (= v (+ 2 1)))";
    assertThat(AbstractFormulaManager.tokenize(part1 + part2)).containsExactly(part1, part2);
  }

  @Test
  public void skipWhitespace() {
    String part1 = "(define-const ";
    String part2 = "v Int)";
    String part3 = "(assert ";
    String part4 = "(= v (+ 2 1)))";
    String smtlib = " " + part1 + " " + part2 + " \n" + part3 + "\n" + part4;
    assertThat(AbstractFormulaManager.tokenize(smtlib))
        .containsExactly(part1 + part2, part3 + part4);
  }

  @Test
  public void windowsNewlines() {
    String part1 = "(define-const ";
    String part2 = "v Int)";
    String smtlib = part1 + "\r\n" + part2;
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(part1 + part2);
  }

  @Test
  public void avoidLinewraps() {
    String smtlib = "(define-const;comment\nv\nInt)";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly("(define-const v Int)");
  }

  @Test
  public void newlineInString() {
    String smtlib = "(assert (= v \"\n\"))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void newlineInQuotedSymbol() {
    String smtlib = "(assert (= |\n| 0))";
    assertThat(AbstractFormulaManager.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void tokenTest() {
    String smtlib = "(assert\n(= v (+ 2 1)))";
    String token = AbstractFormulaManager.tokenize(smtlib).get(0);
    assertThat(token).isEqualTo("(assert (= v (+ 2 1)))");
    assertThat(AbstractFormulaManager.isAssertToken(token)).isTrue();
  }

  @Test
  public void tokenTestBroken() {
    String smtlib = "(assert (= v \"\n\"))";
    String token = AbstractFormulaManager.tokenize(smtlib).get(0);
    assertThat(token).isEqualTo(smtlib);
    assertThat(AbstractFormulaManager.isAssertToken(token)).isTrue();
  }
}
