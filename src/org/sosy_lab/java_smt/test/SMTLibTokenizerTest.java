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

import com.google.common.truth.Truth;
import org.junit.Test;
import org.sosy_lab.java_smt.basicimpl.SMTLibTokenizer;

public class SMTLibTokenizerTest {
  @Test
  public void parenthesesTest() {
    // Valid input string
    String validBrackets = "(assert (= 3 (+ 2 1)))";
    Truth.assertThat(SMTLibTokenizer.of(validBrackets).toImmutableList())
        .containsExactly(validBrackets);

    // Same string, but with one too many closing brackets
    String invalidClose = "(assert (= 3 (+ 2 1))))";
    assertThrows(
        IllegalArgumentException.class, () -> SMTLibTokenizer.of(invalidClose).toImmutableList());

    // Same string, but with a missing closing bracket
    String invalidOpen = "(assert (= 3 (+ 2 1))";
    assertThrows(
        IllegalArgumentException.class, () -> SMTLibTokenizer.of(invalidOpen).toImmutableList());

    // Valid input string with an escaped ')' as part of a comment
    // This should not confuse the tokenizer!
    String inComment = "(assert (= 3;)\n(- 4 1)))";
    assertThat(SMTLibTokenizer.of(inComment).toImmutableList())
        .containsExactly("(assert (= 3\n(- 4 1)))");

    // Valid input string with an escaped ')' as part of a string literal
    String inString = "(assert (= v \")\"))";
    assertThat(SMTLibTokenizer.of(inString).toImmutableList()).containsExactly(inString);

    // Valid input string with an escaped ')' as part of a quoted symbol
    String inQuotedSymbol = "(assert (= |)v| 0))";
    assertThat(SMTLibTokenizer.of(inQuotedSymbol).toImmutableList())
        .containsExactly(inQuotedSymbol);
  }

  @Test
  public void newlineTest() {
    // Split string between commands
    String splitCmd1 = "(define-const v Int)";
    String splitCmd2 = "(assert (= v (+ 2 1)))";
    assertThat(SMTLibTokenizer.of(splitCmd1 + " \n " + splitCmd2).toImmutableList())
        .containsExactly(splitCmd1, splitCmd2);

    // Ignore whitespace between commands
    String skipWhitespace1 = "(define-const \n v Int)";
    String skipWhitespace2 = "(assert \n(= v (+ 2 1)))";
    assertThat(
            SMTLibTokenizer.of(" " + skipWhitespace1 + " \n" + skipWhitespace2 + "\n")
                .toImmutableList())
        .containsExactly(skipWhitespace1, skipWhitespace2);

    // Copy windows newlines in the commands
    String windowsNewlines = "(define-const\r\nv Int)";
    assertThat(SMTLibTokenizer.of(windowsNewlines).toImmutableList())
        .containsExactly(windowsNewlines);

    // Avoid connecting tokens across line-wraps when comments are removed
    String avoidWrap = "(define-const;comment\nv\nInt)";
    assertThat(SMTLibTokenizer.of(avoidWrap).toImmutableList())
        .containsExactly("(define-const\nv\nInt)");

    // Copy newline characters in strings
    String inString = "(assert (= v \"\n\"))";
    assertThat(SMTLibTokenizer.of(inString).toImmutableList()).containsExactly(inString);

    // Copy newline characters in quoted symbols
    String inQuotedSymbol = "(assert (= |\n| 0))";
    assertThat(SMTLibTokenizer.of(inQuotedSymbol).toImmutableList())
        .containsExactly(inQuotedSymbol);
  }

  @Test
  public void tokenTest() {
    // Tests if (assert... ) command is recognized
    String tokenSMTLIB = "(assert\n(= v (+ 2 1)))";
    String token = SMTLibTokenizer.of(tokenSMTLIB).iterator().next();
    assertThat(token).isEqualTo(tokenSMTLIB);
    assertThat(SMTLibTokenizer.isAssertToken(token)).isTrue();

    // Test if (assert... ) command is recognized when it goes across several lines
    String stringTokenSMTLIB = "(assert (= v \"\n\"))";
    String stringToken = SMTLibTokenizer.of(stringTokenSMTLIB).iterator().next();
    assertThat(stringToken).isEqualTo(stringTokenSMTLIB);
    assertThat(SMTLibTokenizer.isAssertToken(stringToken)).isTrue();
  }
}
