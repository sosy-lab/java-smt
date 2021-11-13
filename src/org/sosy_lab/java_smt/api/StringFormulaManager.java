// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

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

  NumeralFormula.IntegerFormula length(StringFormula str);

  StringFormula concat(StringFormula str1, StringFormula str2);

  /**
   * @param str formula representing the string to match
   * @param regex formula representing the regular expression
   * @return a formula representing the acceptance of the string by the regular expression
   */
  BooleanFormula in(StringFormula str, RegexFormula regex);

  /**
   * Returns a {@link RegexFormula} representing the given constant.
   *
   * @param value the regular expression the returned <code>Formula</code> should represent
   * @return a Formula representing the given value
   */
  RegexFormula makeRegex(String value);

  // basic regex operations

  /** @return formula denoting the empty set of strings */
  RegexFormula none();

  /** @return formula denoting the set of all strings */
  RegexFormula all();

  /** @return formula denoting the set of all strings of length 1 */
  RegexFormula allChar();

  /** @return formula denoting the concatenation */
  RegexFormula concat(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the union */
  RegexFormula union(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the intersection */
  RegexFormula intersection(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the Kleene closure */
  RegexFormula complement(RegexFormula regex);

  /** @return formula denoting the Kleene closure (0 or more) */
  RegexFormula closure(RegexFormula regex);

  // derived regex operations

  /** @return formula denoting the difference */
  RegexFormula difference(RegexFormula regex1, RegexFormula regex2);

  /** @return formula denoting the Kleene cross (1 or more) */
  RegexFormula cross(RegexFormula regex);

  /** @return formula denoting the optionality */
  RegexFormula optional(RegexFormula regex);

  /** @return formula denoting the concatenation n times */
  RegexFormula times(RegexFormula regex, int repetitions);
}
