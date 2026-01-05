/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager.SymbolManager;

public class ParsingStringFormulaManager implements StringFormulaManager {
  private final SymbolManager symbolManager;
  private final StringFormulaManager delegate;

  public ParsingStringFormulaManager(SymbolManager pSymbolManager, StringFormulaManager pDelegate) {
    symbolManager = pSymbolManager;
    delegate = pDelegate;
  }

  @Override
  public StringFormula makeString(String value) {
    return delegate.makeString(value);
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    var term = delegate.makeVariable(pVar);
    symbolManager.addConstant(pVar, term);
    return term;
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    return delegate.equal(str1, str2);
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    return delegate.greaterThan(str1, str2);
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    return delegate.greaterOrEquals(str1, str2);
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    return delegate.lessThan(str1, str2);
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    return delegate.lessOrEquals(str1, str2);
  }

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    return delegate.prefix(prefix, str);
  }

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    return delegate.suffix(suffix, str);
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    return delegate.contains(str, part);
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    return delegate.indexOf(str, part, startIndex);
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    return delegate.charAt(str, index);
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    return delegate.substring(str, index, length);
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    return delegate.replace(fullStr, target, replacement);
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    return delegate.replaceAll(fullStr, target, replacement);
  }

  @Override
  public IntegerFormula length(StringFormula str) {
    return delegate.length(str);
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    return delegate.concat(parts);
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    return delegate.in(str, regex);
  }

  @Override
  public RegexFormula makeRegex(String value) {
    return delegate.makeRegex(value);
  }

  @Override
  public RegexFormula none() {
    return delegate.none();
  }

  @Override
  public RegexFormula all() {
    return delegate.all();
  }

  @Override
  public RegexFormula allChar() {
    return delegate.allChar();
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    return delegate.range(start, end);
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    return delegate.concatRegex(parts);
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    return delegate.union(regex1, regex2);
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    return delegate.intersection(regex1, regex2);
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    return delegate.complement(regex);
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    return delegate.closure(regex);
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    return delegate.difference(regex1, regex2);
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    return delegate.cross(regex);
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    return delegate.optional(regex);
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    return delegate.times(regex, repetitions);
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    return delegate.toIntegerFormula(str);
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    return delegate.toStringFormula(number);
  }

  @Override
  public IntegerFormula toCodePoint(StringFormula str) {
    return delegate.toCodePoint(str);
  }

  @Override
  public StringFormula fromCodePoint(IntegerFormula codePoint) {
    return delegate.fromCodePoint(codePoint);
  }
}
