/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

@SuppressWarnings("UnusedVariable")
public class PortfolioStringFormulaManager implements StringFormulaManager {

  private final PortfolioFormulaCreator creator;

  public PortfolioStringFormulaManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
  }

  @Override
  public StringFormula makeString(String value) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public IntegerFormula length(StringFormula str) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula makeRegex(String value) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula none() {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula all() {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula allChar() {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public IntegerFormula toCodePoint(StringFormula str) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public StringFormula fromCodePoint(IntegerFormula codePoint) {
    throw new UnsupportedOperationException("implement me");
  }
}
