// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.base.Preconditions;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

/**
 * Manager for dealing with string formulas. Functions come from <a
 * href="http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml">String theory in SMTLIB</a>.
 */
public interface StringFormulaManager {

  /**
   * Creates a {@link StringFormula} representing the given constant String.
   *
   * <p>The String argument is expected to be a regular Java String and may contain Unicode
   * characters from the first 3 planes (codepoints 0x00000-0x2FFFFF). Higher codepoints are not
   * allowed due to limitations in SMTLIB. We do not support SMTLIB escape sequences in this method,
   * and String like <code>"\\u{abc}"</code> are read verbatim and are not substituted with their
   * Unicode character. If you still want to use SMTLIB Strings with this method, the function
   * {@link AbstractStringFormulaManager#unescapeUnicodeForSmtlib(String)} can be used to handle the
   * conversion before calling this method. Note that you may then also have to use {@link
   * AbstractStringFormulaManager#escapeUnicodeForSmtlib(String)} to convert Strings from the model
   * back to a format that is compatible with other SMTLIB based solvers.
   *
   * @param value the string value the returned {@link StringFormula} should represent
   * @return a {@link StringFormula} representing the given value
   */
  StringFormula makeString(String value);

  /**
   * Creates a variable of type String with exactly the given name.
   *
   * <p>This variable (symbol) represents a "String" for which the SMT solver needs to find a model.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  StringFormula makeVariable(String pVar);

  // TODO: There is currently no way to use variables of type "Regex", i.e., that represent full
  //       regular expression for which the SMT solver need to find a model.
  //       The reason for this is that the current SMT solvers do not support this feature.
  //       However, we can build a RegexFormula from basic parts like Strings (including
  //       variables of type String) and operations like range, union, or complement.

  BooleanFormula equal(StringFormula str1, StringFormula str2);

  BooleanFormula greaterThan(StringFormula str1, StringFormula str2);

  BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2);

  BooleanFormula lessThan(StringFormula str1, StringFormula str2);

  BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2);

  /** Check whether the given prefix is a real prefix of str. */
  BooleanFormula prefix(StringFormula prefix, StringFormula str);

  /** Check whether the given suffix is a real suffix of str. */
  BooleanFormula suffix(StringFormula suffix, StringFormula str);

  BooleanFormula contains(StringFormula str, StringFormula part);

  /**
   * Get the first index for a substring in a String, or -1 if the substring is not found.
   * startIndex (inlcuded) denotes the start of the search for the index.
   */
  IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex);

  /**
   * Get a substring of length 1 from the given String if the given index is within bounds.
   * Otherwise, returns an empty string.
   */
  StringFormula charAt(StringFormula str, IntegerFormula index);

  /**
   * Get a substring from the given String.
   *
   * <p>The result is underspecified, if the start index is out of bounds for the given String or if
   * the requested length is negative. The length of the result is the minimum of the requested
   * length and the remaining length of the given String.
   */
  StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length);

  /** Replace the first appearances of target in fullStr with the replacement. */
  StringFormula replace(StringFormula fullStr, StringFormula target, StringFormula replacement);

  /** Replace all appearances of target in fullStr with the replacement. */
  StringFormula replaceAll(StringFormula fullStr, StringFormula target, StringFormula replacement);

  IntegerFormula length(StringFormula str);

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

  /**
   * @return formula denoting the empty set of strings
   */
  RegexFormula none();

  /**
   * Note: The size of the used alphabet depends on the underlying SMT solver.
   *
   * @return formula denoting the set of all strings, also known as Regex <code>".*"</code>.
   */
  RegexFormula all();

  /**
   * Note: The size of the used alphabet depends on the underlying SMT solver.
   *
   * @return formula denoting the set of all strings of length 1, also known as DOT operator which
   *     represents one arbitrary char, or as Regex <code>"."</code>.
   */
  RegexFormula allChar();

  /**
   * @return formula denoting the range regular expression over two sequences of length 1.
   */
  RegexFormula range(StringFormula start, StringFormula end);

  /**
   * @return formula denoting the range regular expression over two chars.
   * @see #range(StringFormula, StringFormula)
   */
  default RegexFormula range(char start, char end) {
    Preconditions.checkArgument(
        start <= end,
        "Range from start '%s' (%s) to end '%s' (%s) is empty.",
        start,
        (int) start,
        end,
        (int) end);
    return range(makeString(String.valueOf(start)), makeString(String.valueOf(end)));
  }

  /**
   * @return formula denoting the concatenation
   */
  default RegexFormula concat(RegexFormula... parts) {
    return concatRegex(Arrays.asList(parts));
  }

  /**
   * @return formula denoting the concatenation
   */
  // TODO the naming of this function collides with #concat(List<StringFormula>).
  //  Maybe we should split String and Regex manager.
  RegexFormula concatRegex(List<RegexFormula> parts);

  /**
   * @return formula denoting the union
   */
  RegexFormula union(RegexFormula regex1, RegexFormula regex2);

  /**
   * @return formula denoting the intersection
   */
  RegexFormula intersection(RegexFormula regex1, RegexFormula regex2);

  /**
   * @return formula denoting the Kleene closure
   */
  RegexFormula complement(RegexFormula regex);

  /**
   * @return formula denoting the Kleene closure (0 or more), also known as STAR operand.
   */
  RegexFormula closure(RegexFormula regex);

  // derived regex operations

  /**
   * @return formula denoting the difference
   */
  RegexFormula difference(RegexFormula regex1, RegexFormula regex2);

  /**
   * @return formula denoting the Kleene cross (1 or more), also known as PLUS operand.
   */
  RegexFormula cross(RegexFormula regex);

  /**
   * @return formula denoting the optionality, also known as QUESTIONMARK operand.
   */
  RegexFormula optional(RegexFormula regex);

  /**
   * @return formula denoting the concatenation n times
   */
  RegexFormula times(RegexFormula regex, int repetitions);

  /**
   * Interpret a String formula as an Integer formula.
   *
   * <p>The number is interpreted in base 10 and has no leading zeros. The method works as expected
   * for positive numbers, including zero. It returns the constant value of <code>-1</code> for
   * negative numbers or invalid number representations, for example if any char is no digit.
   */
  IntegerFormula toIntegerFormula(StringFormula str);

  /**
   * Interpret an Integer formula as a String formula.
   *
   * <p>The number is in base 10. The method works as expected for positive numbers, including zero.
   * It returns the empty string <code>""</code> for negative numbers.
   */
  StringFormula toStringFormula(IntegerFormula number);

  /**
   * Returns an Integer formula representing the code point of the only character of the given
   * String formula, if it represents a single character. Otherwise, returns -1.
   */
  IntegerFormula toCodePoint(StringFormula str);

  /**
   * Returns a String formula representing the single character with the given code point, if it is
   * a valid Unicode code point within the Basic Multilingual Plane (BMP) or planes 1 and 2
   * (codepoints in range [0x00000, 0x2FFFF]). Otherwise, returns the empty string.
   */
  StringFormula fromCodePoint(IntegerFormula codePoint);
}
