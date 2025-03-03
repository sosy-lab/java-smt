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
import org.sosy_lab.java_smt.basicimpl.Tokenizer;

public class TokenizerTest {
  @Test
  public void parenthesesTest() {
    // Valid input string
    String validBrackets = "(assert (= 3 (+ 2 1)))";
    Truth.assertThat(Tokenizer.tokenize(validBrackets)).containsExactly(validBrackets);

    // Same string, but with one too many closing brackets
    String invalidClose = "(assert (= 3 (+ 2 1))))";
    assertThrows(IllegalArgumentException.class, () -> Tokenizer.tokenize(invalidClose));

    // Same string, but with a missing closing bracket
    String invalidOpen = "(assert (= 3 (+ 2 1))";
    assertThrows(IllegalArgumentException.class, () -> Tokenizer.tokenize(invalidOpen));

    // Valid input string with an escaped ')' as part of a comment
    // This should not confuse the tokenizer!
    String inComment = "(assert (= 3;)\n(- 4 1)))";
    assertThat(Tokenizer.tokenize(inComment)).containsExactly("(assert (= 3\n(- 4 1)))");

    // Valid input string with an escaped ')' as part of a string literal
    String inString = "(assert (= v \")\"))";
    assertThat(Tokenizer.tokenize(inString)).containsExactly(inString);

    // Valid input string with an escaped ')' as part of a quoted symbol
    String inQuotedSymbol = "(assert (= |)v| 0))";
    assertThat(Tokenizer.tokenize(inQuotedSymbol)).containsExactly(inQuotedSymbol);
  }

  @Test
  public void newlineTest() {
    // Split string between commands
    String splitCmd1 = "(define-const v Int)";
    String splitCmd2 = "(assert (= v (+ 2 1)))";
    assertThat(Tokenizer.tokenize(splitCmd1 + " \n " + splitCmd2))
        .containsExactly(splitCmd1, splitCmd2);

    // Ignore whitespace between commands
    String skipWhitespace1 = "(define-const \n v Int)";
    String skipWhitespace2 = "(assert \n(= v (+ 2 1)))";
    assertThat(Tokenizer.tokenize(" " + skipWhitespace1 + " \n" + skipWhitespace2 + "\n"))
        .containsExactly(skipWhitespace1, skipWhitespace2);

    // Copy windows newlines in the commands
    String windowsNewlines = "(define-const\r\nv Int)";
    assertThat(Tokenizer.tokenize(windowsNewlines)).containsExactly(windowsNewlines);

    // Avoid connecting tokens across line-wraps when comments are removed
    String avoidWrap = "(define-const;comment\nv\nInt)";
    assertThat(Tokenizer.tokenize(avoidWrap)).containsExactly("(define-const\nv\nInt)");

    // Copy newline characters in strings
    String inString = "(assert (= v \"\n\"))";
    assertThat(Tokenizer.tokenize(inString)).containsExactly(inString);

    // Copy newline characters in quoted symbols
    String inQuotedSymbol = "(assert (= |\n| 0))";
    assertThat(Tokenizer.tokenize(inQuotedSymbol)).containsExactly(inQuotedSymbol);
  }

  @Test
  public void tokenTest() {
    // Tests if (assert... ) command is recognized
    String tokenSMTLIB = "(assert\n(= v (+ 2 1)))";
    String token = Tokenizer.tokenize(tokenSMTLIB).get(0);
    assertThat(token).isEqualTo(tokenSMTLIB);
    assertThat(Tokenizer.isAssertToken(token)).isTrue();

    // Test if (assert... ) command is recognized when it goes across several lines
    String stringTokenSMTLIB = "(assert (= v \"\n\"))";
    String stringToken = Tokenizer.tokenize(stringTokenSMTLIB).get(0);
    assertThat(stringToken).isEqualTo(stringTokenSMTLIB);
    assertThat(Tokenizer.isAssertToken(stringToken)).isTrue();
  }
}
