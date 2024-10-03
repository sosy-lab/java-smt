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

import com.google.common.truth.Truth;
import org.junit.Test;
import org.sosy_lab.java_smt.basicimpl.Tokenizer;

public class TokenizerTest {
  @Test
  public void validBrackets() {
    String smtlib = "(assert (= 3 (+ 2 1)))";
    Truth.assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test(expected = IllegalArgumentException.class)
  public void invalidClose() {
    String smtlib = "(assert (= 3 (+ 2 1))))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test(expected = IllegalArgumentException.class)
  public void invalidOpen() {
    String smtlib = "(assert (= 3 (+ 2 1))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void parenthesesInComment() {
    String smtlib = "(assert (= 3;)\n(- 4 1)))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly("(assert (= 3\n(- 4 1)))");
  }

  @Test
  public void parenthesesInString() {
    String smtlib = "(assert (= v \")\"))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void parenthesesInQuotedSymbol() {
    String smtlib = "(assert (= |)v| 0))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void splitCommands() {
    String part1 = "(define-const v Int)";
    String part2 = "(assert (= v (+ 2 1)))";
    assertThat(Tokenizer.tokenize(part1 + part2)).containsExactly(part1, part2);
  }

  @Test
  public void skipWhitespace() {
    String part1 = "(define-const \n v Int)";
    String part2 = "(assert \n(= v (+ 2 1)))";
    String smtlib = " " + part1 + " \n" + part2 + "\n";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(part1, part2);
  }

  @Test
  public void windowsNewlines() {
    String smtlib = "(define-const\r\nv Int)";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void avoidLinewraps() {
    String smtlib = "(define-const;comment\nv\nInt)";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly("(define-const\nv\nInt)");
  }

  @Test
  public void newlineInString() {
    String smtlib = "(assert (= v \"\n\"))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void newlineInQuotedSymbol() {
    String smtlib = "(assert (= |\n| 0))";
    assertThat(Tokenizer.tokenize(smtlib)).containsExactly(smtlib);
  }

  @Test
  public void tokenTest() {
    String smtlib = "(assert\n(= v (+ 2 1)))";
    String token = Tokenizer.tokenize(smtlib).get(0);
    assertThat(token).isEqualTo(smtlib);
    assertThat(Tokenizer.isAssertToken(token)).isTrue();
  }

  @Test
  public void tokenTestWithString() {
    String smtlib = "(assert (= v \"\n\"))";
    String token = Tokenizer.tokenize(smtlib).get(0);
    assertThat(token).isEqualTo(smtlib);
    assertThat(Tokenizer.isAssertToken(token)).isTrue();
  }
}
