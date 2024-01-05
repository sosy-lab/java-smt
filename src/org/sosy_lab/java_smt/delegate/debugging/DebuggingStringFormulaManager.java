// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

public class DebuggingStringFormulaManager extends FormulaChecks implements StringFormulaManager {
  private final StringFormulaManager delegate;

  public DebuggingStringFormulaManager(
      StringFormulaManager pDelegate, Set<Formula> pformulasInContext) {
    super(pformulasInContext);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public StringFormula makeString(String value) {
    assertThreadLocal();
    StringFormula result = delegate.makeString(value);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    assertThreadLocal();
    StringFormula result = delegate.makeVariable(pVar);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    assertThreadLocal();
    assertFormulaInContext(str1);
    assertFormulaInContext(str2);
    BooleanFormula result = delegate.equal(str1, str2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    assertThreadLocal();
    assertFormulaInContext(str1);
    assertFormulaInContext(str2);
    BooleanFormula result = delegate.greaterThan(str1, str2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    assertThreadLocal();
    assertFormulaInContext(str1);
    assertFormulaInContext(str2);
    BooleanFormula result = delegate.equal(str1, str2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    assertThreadLocal();
    assertFormulaInContext(str1);
    assertFormulaInContext(str2);
    BooleanFormula result = delegate.lessThan(str1, str2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    assertThreadLocal();
    assertFormulaInContext(str1);
    assertFormulaInContext(str2);
    BooleanFormula result = delegate.lessOrEquals(str1, str2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    assertThreadLocal();
    assertFormulaInContext(prefix);
    assertFormulaInContext(str);
    BooleanFormula result = delegate.prefix(prefix, str);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    assertThreadLocal();
    assertFormulaInContext(suffix);
    assertFormulaInContext(str);
    BooleanFormula result = delegate.suffix(suffix, str);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    assertThreadLocal();
    assertFormulaInContext(str);
    assertFormulaInContext(part);
    BooleanFormula result = delegate.contains(str, part);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    assertThreadLocal();
    assertFormulaInContext(str);
    assertFormulaInContext(part);
    assertFormulaInContext(startIndex);
    IntegerFormula result = delegate.indexOf(str, part, startIndex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    assertThreadLocal();
    assertFormulaInContext(str);
    assertFormulaInContext(index);
    StringFormula result = delegate.charAt(str, index);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    assertThreadLocal();
    assertFormulaInContext(str);
    assertFormulaInContext(index);
    assertFormulaInContext(length);
    StringFormula result = delegate.substring(str, index, length);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    assertThreadLocal();
    assertFormulaInContext(fullStr);
    assertFormulaInContext(target);
    assertFormulaInContext(replacement);
    StringFormula result = delegate.replace(fullStr, target, replacement);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    assertThreadLocal();
    assertFormulaInContext(fullStr);
    assertFormulaInContext(target);
    assertFormulaInContext(replacement);
    StringFormula result = delegate.replaceAll(fullStr, target, replacement);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public IntegerFormula length(StringFormula str) {
    assertThreadLocal();
    assertFormulaInContext(str);
    IntegerFormula result = delegate.length(str);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    assertThreadLocal();
    for (StringFormula t : parts) {
      assertFormulaInContext(t);
    }
    StringFormula result = delegate.concat(parts);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    assertThreadLocal();
    assertFormulaInContext(str);
    assertFormulaInContext(regex);
    BooleanFormula result = delegate.in(str, regex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula makeRegex(String value) {
    assertThreadLocal();
    RegexFormula result = delegate.makeRegex(value);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula none() {
    assertThreadLocal();
    RegexFormula result = delegate.none();
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula all() {
    assertThreadLocal();
    RegexFormula result = delegate.all();
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula allChar() {
    assertThreadLocal();
    RegexFormula result = delegate.allChar();
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    assertThreadLocal();
    assertFormulaInContext(start);
    assertFormulaInContext(end);
    RegexFormula result = delegate.range(start, end);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    assertThreadLocal();
    for (RegexFormula t : parts) {
      assertFormulaInContext(t);
    }
    RegexFormula result = delegate.concatRegex(parts);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    assertThreadLocal();
    assertFormulaInContext(regex1);
    assertFormulaInContext(regex2);
    RegexFormula result = delegate.union(regex1, regex2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    assertThreadLocal();
    assertFormulaInContext(regex1);
    assertFormulaInContext(regex2);
    RegexFormula result = delegate.intersection(regex1, regex2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    assertThreadLocal();
    assertFormulaInContext(regex);
    RegexFormula result = delegate.complement(regex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    assertThreadLocal();
    assertFormulaInContext(regex);
    RegexFormula result = delegate.closure(regex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    assertThreadLocal();
    assertFormulaInContext(regex1);
    assertFormulaInContext(regex2);
    RegexFormula result = delegate.difference(regex1, regex2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    assertThreadLocal();
    assertFormulaInContext(regex);
    RegexFormula result = delegate.cross(regex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    assertThreadLocal();
    assertFormulaInContext(regex);
    RegexFormula result = delegate.optional(regex);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    assertThreadLocal();
    assertFormulaInContext(regex);
    RegexFormula result = delegate.times(regex, repetitions);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    assertThreadLocal();
    assertFormulaInContext(str);
    IntegerFormula result = delegate.toIntegerFormula(str);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    StringFormula result = delegate.toStringFormula(number);
    addFormulaToContext(result);
    return result;
  }
}
