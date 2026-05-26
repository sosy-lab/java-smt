// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

public class DebuggingStringFormulaManager implements StringFormulaManager {
  private final StringFormulaManager delegate;
  private final DebuggingAssertions debugging;

  DebuggingStringFormulaManager(StringFormulaManager pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public StringFormula makeString(String value) {
    debugging.assertThreadLocal();
    StringFormula result = delegate.makeString(value);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    debugging.assertThreadLocal();
    StringFormula result = delegate.makeVariable(pVar);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str1);
    debugging.assertFormulaInContext(str2);
    BooleanFormula result = delegate.equal(str1, str2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str1);
    debugging.assertFormulaInContext(str2);
    BooleanFormula result = delegate.greaterThan(str1, str2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str1);
    debugging.assertFormulaInContext(str2);
    BooleanFormula result = delegate.equal(str1, str2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str1);
    debugging.assertFormulaInContext(str2);
    BooleanFormula result = delegate.lessThan(str1, str2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str1);
    debugging.assertFormulaInContext(str2);
    BooleanFormula result = delegate.lessOrEquals(str1, str2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(prefix);
    debugging.assertFormulaInContext(str);
    BooleanFormula result = delegate.prefix(prefix, str);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(suffix);
    debugging.assertFormulaInContext(str);
    BooleanFormula result = delegate.suffix(suffix, str);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    debugging.assertFormulaInContext(part);
    BooleanFormula result = delegate.contains(str, part);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    debugging.assertFormulaInContext(part);
    debugging.assertFormulaInContext(startIndex);
    IntegerFormula result = delegate.indexOf(str, part, startIndex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    debugging.assertFormulaInContext(index);
    StringFormula result = delegate.charAt(str, index);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    debugging.assertFormulaInContext(index);
    debugging.assertFormulaInContext(length);
    StringFormula result = delegate.substring(str, index, length);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(fullStr);
    debugging.assertFormulaInContext(target);
    debugging.assertFormulaInContext(replacement);
    StringFormula result = delegate.replace(fullStr, target, replacement);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(fullStr);
    debugging.assertFormulaInContext(target);
    debugging.assertFormulaInContext(replacement);
    StringFormula result = delegate.replaceAll(fullStr, target, replacement);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula length(StringFormula str) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    IntegerFormula result = delegate.length(str);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    debugging.assertThreadLocal();
    for (StringFormula t : parts) {
      debugging.assertFormulaInContext(t);
    }
    StringFormula result = delegate.concat(parts);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    debugging.assertFormulaInContext(regex);
    BooleanFormula result = delegate.in(str, regex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula makeRegex(String value) {
    debugging.assertThreadLocal();
    RegexFormula result = delegate.makeRegex(value);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula none() {
    debugging.assertThreadLocal();
    RegexFormula result = delegate.none();
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula all() {
    debugging.assertThreadLocal();
    RegexFormula result = delegate.all();
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula allChar() {
    debugging.assertThreadLocal();
    RegexFormula result = delegate.allChar();
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(start);
    debugging.assertFormulaInContext(end);
    RegexFormula result = delegate.range(start, end);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    debugging.assertThreadLocal();
    for (RegexFormula t : parts) {
      debugging.assertFormulaInContext(t);
    }
    RegexFormula result = delegate.concatRegex(parts);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex1);
    debugging.assertFormulaInContext(regex2);
    RegexFormula result = delegate.union(regex1, regex2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex1);
    debugging.assertFormulaInContext(regex2);
    RegexFormula result = delegate.intersection(regex1, regex2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex);
    RegexFormula result = delegate.complement(regex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex);
    RegexFormula result = delegate.closure(regex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex1);
    debugging.assertFormulaInContext(regex2);
    RegexFormula result = delegate.difference(regex1, regex2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex);
    RegexFormula result = delegate.cross(regex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex);
    RegexFormula result = delegate.optional(regex);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(regex);
    RegexFormula result = delegate.times(regex, repetitions);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    IntegerFormula result = delegate.toIntegerFormula(str);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    StringFormula result = delegate.toStringFormula(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula toCodePoint(StringFormula str) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(str);
    IntegerFormula result = delegate.toCodePoint(str);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public StringFormula fromCodePoint(IntegerFormula codepoint) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(codepoint);
    StringFormula result = delegate.fromCodePoint(codepoint);
    debugging.addFormulaTerm(result);
    return result;
  }
}
