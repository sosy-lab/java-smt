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

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableList;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Optional;

/**
 * Helper class for splitting up an SMT-LIB2 file into a string of commands.
 *
 * <p>This is not a full SMTLIB parser, but only provides basic support for SMTLIB commands.
 */
public final class Tokenizer {

  private Tokenizer() {}

  /** Variable names (symbols) can be wrapped with "|". This function removes those chars. */
  public static String dequote(String s) {
    int l = s.length();
    if (s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
  }

  /**
   * Split up a sequence of lisp expressions into a list of nen-empty tokens. This method simply
   * uses the {@link TokenizerIterator} and creates a list out of all tokens.
   *
   * <p>This is used by {@link AbstractFormulaManager#parse(String)} as part of the preprocessing
   * before the input is passed on to the solver. SMT-LIB2 scripts are sequences of commands that
   * are just r-expression. We split them up and then return the list.
   *
   * <p>As an example <code>tokenize("(define-const a Int)(assert (= a 0)")</code> will return the
   * sequence <code>["(define-const a Int)", "(assert (= a 0))"]</code>
   */
  public static ImmutableList<String> tokenizeToList(String input) {
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    TokenizerIterator iter = new TokenizerIterator(input);

    // TODO: Switch to some one-liner like: iter.forEachRemaining(builder::add);
    while (iter.hasNext()) {
      final String token = iter.next();
      checkState(!token.isEmpty());
      builder.add(token);
    }
    return builder.build();
  }

  private static boolean matchesOneOf(String token, String... regexp) {
    return token.matches("\\(\\s*(" + String.join("|", regexp) + ")[\\S\\s]*");
  }

  /**
   * Check if the token is <code>(set-logic ..)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isSetLogicToken(String token) {
    return matchesOneOf(token, "set-logic");
  }

  public static boolean isSetInfoToken(String token) {
    return matchesOneOf(token, "set-info");
  }

  /**
   * Check if the token is a function or variable declaration.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isDeclarationToken(String token) {
    return matchesOneOf(token, "declare-const", "declare-fun");
  }

  /**
   * Check if the token is a function definition.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isDefinitionToken(String token) {
    return matchesOneOf(token, "define-fun", "define-const");
  }

  /**
   * Check if the token is an <code>(assert ...)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isAssertToken(String token) {
    return matchesOneOf(token, "assert");
  }

  /**
   * Check if the token is an <code>(push ...)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isPushToken(String token) {
    return matchesOneOf(token, "push");
  }

  /**
   * Check if the token is an <code>(pop ...)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isPopToken(String token) {
    return matchesOneOf(token, "pop");
  }

  /**
   * Check if the token is an <code>(reset-assertions ...)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isResetAssertionsToken(String token) {
    return matchesOneOf(token, "reset-assertions");
  }

  /**
   * Check if the token is an <code>(reset)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isResetToken(String token) {
    return matchesOneOf(token, "reset");
  }

  /**
   * Check if the token is <code>(exit)</code>.
   *
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
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
   * <p>Use {@link #tokenizeToList(String)} to turn an SMT-LIB2 script into a string of input
   * tokens.
   */
  public static boolean isForbiddenToken(String token) {
    return isPushToken(token)
        || isPopToken(token)
        || isResetAssertionsToken(token)
        || isResetToken(token);
  }

  public static final class TokenizerIterator implements Iterator<String> {

    private final String input;
    private final int inputLength;

    // To avoid empty string returns we have a 1-lookahead. If this is ever empty, we don't have
    // a next element!
    private Optional<String> nextToken = Optional.empty();

    private boolean inComment = false;
    private boolean inString = false;
    private boolean inQuoted = false;

    private int level = 0;
    private int pos = 0;

    /**
     * Returns an {@link Iterator} splitting up the given {@link String}, consisting of a sequence
     * of lisp expressions (i.e. SMTLIB2), into non-empty SMTLIB2 tokens.
     *
     * <p>SMT-LIB2 scripts are sequences of commands that are just r-expression. Split them up for
     * (pre-/post-)processing makes handling easier. This is used by e.g. {@link
     * AbstractFormulaManager#parse(String)} as part of the preprocessing before the input is passed
     * on to the solver.
     *
     * <p>As an example <code>tokenize("(define-const a Int)(assert (= a 0)")</code> will return the
     * following tokens: <code>["(define-const a Int)", "(assert (= a 0))"]</code>
     *
     * @param inputToTokenize SMTLIB2 {@link String}.
     */
    private TokenizerIterator(final String inputToTokenize) {
      input = inputToTokenize;
      inputLength = input.length();

      // Generate first token if possible. There might be none, in which case isNext() needs to
      // return 'false' immediately.
      while (nextToken.isEmpty() && !endOfInputReached()) {
        String maybeFirstToken = getNextPossiblyEmptyToken();
        // Can be optimized by returning null for empty tokens in getNextPossiblyEmptyToken()
        if (!maybeFirstToken.isEmpty()) {
          nextToken = Optional.of(maybeFirstToken);
        }
      }
    }

    private boolean endOfInputReached() {
      // As long as pos is smaller than inputLength, we are not at the end of the input. This
      // does not tell us that there is still tokens left! There might be input that we skip!
      return pos >= inputLength;
    }

    @Override
    public boolean hasNext() {
      return nextToken.isPresent();
    }

    @Override
    public String next() {
      if (!hasNext()) {
        throw new NoSuchElementException();
      }

      String currentToken = nextToken.orElseThrow();
      nextToken = Optional.empty();

      // Get lookahead if possible
      while (!endOfInputReached()) {
        String maybeNextToken = getNextPossiblyEmptyToken();
        // Can be optimized by returning null for empty tokens in getNextPossiblyEmptyToken()
        if (!maybeNextToken.isEmpty()) {
          nextToken = Optional.of(maybeNextToken);
          break;
        }
      }
      // nextToken may be present or empty!
      return checkNotNull(currentToken);
    }

    private String getNextPossiblyEmptyToken() {
      StringBuilder tokenBuilder = new StringBuilder();
      String token = null;

      while (token == null && !endOfInputReached()) {
        char c = input.charAt(pos);
        if (inComment) {
          if (c == '\n') {
            // End of a comment
            inComment = false;
            if (level > 0) {
              // If we're in an expression we need to replace the entire comment (+ the newline)
              // with
              // some whitespace. Otherwise, symbols might get merged across line-wraps. This is not
              // a problem at the top-level where all terms are surrounded by brackets.
              tokenBuilder.append(c);
            }
          }

        } else if (inString) {
          if (c == '"') {
            // We have a double quote: Check that it's not followed by another and actually closes
            // the string.
            Optional<Character> n =
                (pos == inputLength - 1) ? Optional.empty() : Optional.of(input.charAt(pos + 1));
            if (n.isEmpty() || n.orElseThrow() != '"') {
              // Close the string
              tokenBuilder.append(c);
              inString = false;
            } else {
              // Add both quotes to the token and skip one character ahead
              tokenBuilder.append(c);
              tokenBuilder.append(n.orElseThrow());
              pos++;
            }
          } else {
            tokenBuilder.append(c);
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
          tokenBuilder.append(c);

        } else if (c == ';') {
          // Start of a comment
          inComment = true;

        } else if (c == '"') {
          // Start of a string literal
          inString = true;
          tokenBuilder.append(c);

        } else if (c == '|') {
          // Start of a quoted symbol
          inQuoted = true;
          tokenBuilder.append(c);

        } else {
          // Just a regular character outside of comments, quotes or string literals
          if (level == 0) {
            // We're at the top-level
            if (!Character.isWhitespace(c)) {
              if (c == '(') {
                // Handle opening brackets
                tokenBuilder.append("(");
                level++;
              } else if (c == ')') {
                throw new IllegalArgumentException(
                    "parentheses do not match, unexpected closing parenthesis");
              } else {
                tokenBuilder.append(c);
              }
            } else {
              if (!tokenBuilder.isEmpty()) {
                token = tokenBuilder.toString();
              }
            }
          } else {
            // We're inside an r-expression
            tokenBuilder.append(c);
            // Handle opening/closing brackets
            if (c == '(') {
              level++;
            }
            if (c == ')') {
              if (level == 1) {
                token = tokenBuilder.toString();
              }
              level--;
            }
          }
        }
        pos++;
      }

      if (level != 0) {
        // Throw an exception if the brackets don't match
        throw new IllegalArgumentException("parentheses do not match, too many open parentheses");
      }

      if (token == null) {
        // This is always the empty token. Can only happen at tWe need to fix this first.he end of
        // the input.
        token = tokenBuilder.toString();
      }
      return token;
    }
  }
}
