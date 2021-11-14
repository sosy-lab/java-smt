// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.util.Arrays;
import java.util.List;

/**
 * Manager for dealing with string formulas. Functions come from
 * http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml.
 */
public interface StringFormulaManager {

  /**
   * Returns a {@link StringFormula} representing the given constant.
   *
   * @param value the string value the returned <code>Formula</code> should represent
   * @return a Formula representing the given value
   */
  StringFormula makeString(String value);

  /**
   * Creates a variable with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  StringFormula makeVariable(String pVar);

  BooleanFormula equal(StringFormula str1, StringFormula str2);

  BooleanFormula greaterThan(StringFormula str1, StringFormula str2);

  BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2);

  BooleanFormula lessThan(StringFormula str1, StringFormula str2);

  BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2);

  /** Check whether the given prefix is a real prefix of str. */
  BooleanFormula prefix(StringFormula prefix, StringFormula str);

  /** Check whether the given suffix is a real suffix of str. */
  BooleanFormula suffix(StringFormula suffix, StringFormula str);

  NumeralFormula.IntegerFormula length(StringFormula str);

  default StringFormula concat(StringFormula... parts) {
    return concat(Arrays.asList(parts));
  }

  StringFormula concat(List<StringFormula> parts);

  /**
   * @param str formula representing the string to match
   * @param regex formula representing the regular expression
   * @return a formula representing the acceptance of the string by the regular expression
   */
  BooleanFormula in(StringFormula str, RegexFormula regex);

  /**
   * Returns a {@link RegexFormula} representing the given constant.
   *
   * <p>This method does not parse an existing regex from String, but uses the String directly as a
   * constant.
   *
   * @param value the regular expression the returned <code>Formula</code> should represent
   */
  RegexFormula makeRegex(String value);

  // basic regex operations

  /** @return formula denoting the empty set of strings */
  RegexFormula none();

  /** @return formula denoting the set of all strings, also known as Regex <code>".*"</code>. */
  RegexFormula all();

  /** @return formula denoting the set of all strings of length 1, also known as DOT operator. */
  default RegexFormula allChar() {
    return range(Character.MIN_VALUE, Character.MAX_VALUE);
  }

  /** @return formula denoting the range regular expression over two sequences of length 1. */
  RegexFormula range(StringFormula start, StringFormula end);

  /**
   * @return formula denoting the range regular expression over two chars.
   * @see #range(StringFormula, StringFormula)
   */
  default RegexFormula range(char start, char end) {
    return range(makeString(String.valueOf(start)), makeString(String.valueOf(end)));
  }

  /** @return formula denoting the concatenation */
  default RegexFormula concat(RegexFormula... parts) {
    return concatRegex(Arrays.asList(parts));
  }

  /** @return formula denoting the concatenation */
  // TODO the naming of this function collides with #concat(List<StringFormula>).
  //  Maybe we should split String and Regex manager.
  RegexFormula concatRegex(List<RegexFormula> parts);

  /** @return formula denoting the union */
  RegexFormula union(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the intersection */
  RegexFormula intersection(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the Kleene closure */
  RegexFormula complement(RegexFormula regex);

  /** @return formula denoting the Kleene closure (0 or more), also known as STAR operand. */
  RegexFormula closure(RegexFormula regex);

  // derived regex operations

  /** @return formula denoting the difference */
  RegexFormula difference(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the Kleene cross (1 or more), also known as PLUS operand. */
  RegexFormula cross(RegexFormula regex);

  /** @return formula denoting the optionality, also known as QUESTIONMARK operand. */
  RegexFormula optional(RegexFormula regex);

  /** @return formula denoting the concatenation n times */
  RegexFormula times(RegexFormula regex, int repetitions);
}
