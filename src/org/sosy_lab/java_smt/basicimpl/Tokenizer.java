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

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Optional;

/** Helper class for splitting up an SMT-LIB2 file into a string of commands. */
public final class Tokenizer {

  private Tokenizer() {}

  /**
   * Split up a sequence of lisp expressions.
   *
   * <p>This is used by {@link AbstractFormulaManager#parse(String)} as part of the preprocessing
   * before the input is passed on to the solver. SMT-LIB2 scripts are sequences of commands that
   * are just r-expression. We split them up and then return the list.
   *
   * <p>As an example <code>tokenize("(define-const a Int)(assert (= a 0)")</code> will return the
   * sequence <code>["(define-const a Int)", "(assert (= a 0))"]</code>
   */
  public static List<String> tokenize(String input) {
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    boolean inComment = false;
    boolean inString = false;
    boolean inQuoted = false;

    int level = 0;
    int pos = 0;

    StringBuilder token = new StringBuilder();
    while (pos < input.length()) {
      char c = input.charAt(pos);
      if (inComment) {
        if (c == '\n') {
          // End of a comment
          inComment = false;
          if (level > 0) {
            // If we're in an expression we need to replace the entire comment (+ the newline) with
            // some whitespace. Otherwise symbols might get merged across line-wraps. This is not
            // a problem at the top-level where all terms are surrounded by brackets.
            token.append(c);
          }
        }

      } else if (inString) {
        if (c == '"') {
          // We have a double quote: Check that it's not followed by another and actually closes
          // the string.
          Optional<Character> n =
              (pos == input.length() - 1) ? Optional.empty() : Optional.of(input.charAt(pos + 1));
          if (n.isEmpty() || n.orElseThrow() != '"') {
            // Close the string
            token.append(c);
            inString = false;
          } else {
            // Add both quotes to the token and skip one character ahead
            token.append(c);
            token.append(n.orElseThrow());
            pos++;
          }
        } else {
          token.append(c);
        }

      } else if (inQuoted) {
        if (c == '|') {
          // Close the quotes
          inQuoted = false;
        }
        if (c == '\\') {
          // The SMT-LIB2 standard does not allow backslash inside quoted symbols:
          // Throw an exception
          throw new IllegalArgumentException();
        }
        token.append(c);

      } else if (c == ';') {
        // Start of a comment
        inComment = true;

      } else if (c == '"') {
        // Start of a string literal
        inString = true;
        token.append(c);

      } else if (c == '|') {
        // Start of a quoted symbol
        inQuoted = true;
        token.append(c);

      } else {
        // Just a regular character outside of comments, quotes or string literals
        if (level == 0) {
          // We're at the top-level
          if (!Character.isWhitespace(c)) {
            if (c == '(') {
              // Handle opening brackets
              token.append("(");
              level++;
            } else {
              // Should be unreachable: all top-level expressions need parentheses around them
              throw new IllegalArgumentException();
            }
          }
        } else {
          // We're inside an r-expression
          token.append(c);
          // Handle opening/closing brackets
          if (c == '(') {
            level++;
          }
          if (c == ')') {
            if (level == 1) {
              builder.add(token.toString());
              token = new StringBuilder();
            }
            level--;
          }
        }
      }
      pos++;
    }
    if (level != 0) {
      // Throw an exception if the brackets don't match
      throw new IllegalArgumentException();
    }
    return builder.build();
  }

  private static boolean matchesOneOf(String token, String... regexp) {
    return token.matches("\\(\\s*(" + String.join("|", regexp) + ")[\\S\\s]*");
  }

  /**
   * Check if the token is <code>(set-logic ..)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isSetLogicToken(String token) {
    return matchesOneOf(token, "set-logic");
  }

  /**
   * Check if the token is a function or variable declaration.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isDeclarationToken(String token) {
    return matchesOneOf(token, "declare-const", "declare-fun");
  }

  /**
   * Check if the token is a function definition.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isDefinitionToken(String token) {
    return matchesOneOf(token, "define-fun");
  }

  /**
   * Check if the token is an <code>(assert ...)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isAssertToken(String token) {
    return matchesOneOf(token, "assert");
  }

  /**
   * Check if the token is an <code>(push ...)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isPushToken(String token) {
    return matchesOneOf(token, "push");
  }

  /**
   * Check if the token is an <code>(pop ...)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isPopToken(String token) {
    return matchesOneOf(token, "pop");
  }

  /**
   * Check if the token is an <code>(reset-assertions ...)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isResetAssertionsToken(String token) {
    return matchesOneOf(token, "reset-assertions");
  }

  /**
   * Check if the token is an <code>(reset)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isResetToken(String token) {
    return matchesOneOf(token, "reset");
  }

  /**
   * Check if the token is <code>(exit)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isExitToken(String token) {
    return matchesOneOf(token, "exit");
  }

  /**
   * Check if this is a forbidden token.
   *
   * <p>The list of forbidden tokens contains:
   *
   * <ul>
   *   <li>push
   *   <li>pop
   *   <li>reset-assertions
   *   <li>reset
   * </ul>
   *
   * <p>Forbidden tokens manipulate the stack and are not supported while parsing SMT-lIB2 string.
   * When a forbidden token is found parsing should be aborted by throwing an {@link
   * IllegalArgumentException} exception.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  public static boolean isForbiddenToken(String token) {
    return isPushToken(token)
        || isPopToken(token)
        || isResetAssertionsToken(token)
        || isResetToken(token);
  }
}
