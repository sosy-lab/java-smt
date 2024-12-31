// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

class StatisticsStringFormulaManager implements StringFormulaManager {

  private final StringFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsStringFormulaManager(StringFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public StringFormula makeString(String value) {
    stats.stringOperations.getAndIncrement();
    return delegate.makeString(value);
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    stats.stringOperations.getAndIncrement();
    return delegate.makeVariable(pVar);
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.equal(str1, str2);
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.greaterThan(str1, str2);
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.greaterOrEquals(str1, str2);
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.lessThan(str1, str2);
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.lessOrEquals(str1, str2);
  }

  @Override
  public NumeralFormula.IntegerFormula length(StringFormula str) {
    stats.stringOperations.getAndIncrement();
    return delegate.length(str);
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    stats.stringOperations.getAndIncrement();
    return delegate.concat(parts);
  }

  @Override
  public BooleanFormula prefix(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.prefix(str1, str2);
  }

  @Override
  public BooleanFormula suffix(StringFormula str1, StringFormula str2) {
    stats.stringOperations.getAndIncrement();
    return delegate.suffix(str1, str2);
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    stats.stringOperations.getAndIncrement();
    return delegate.contains(str, part);
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    stats.stringOperations.getAndIncrement();
    return delegate.indexOf(str, part, startIndex);
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    stats.stringOperations.getAndIncrement();
    return delegate.charAt(str, index);
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    stats.stringOperations.getAndIncrement();
    return delegate.substring(str, index, length);
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    stats.stringOperations.getAndIncrement();
    return delegate.replace(fullStr, target, replacement);
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    stats.stringOperations.getAndIncrement();
    return delegate.replaceAll(fullStr, target, replacement);
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    stats.stringOperations.getAndIncrement();
    return delegate.in(str, regex);
  }

  @Override
  public RegexFormula makeRegex(String value) {
    stats.stringOperations.getAndIncrement();
    return delegate.makeRegex(value);
  }

  @Override
  public RegexFormula none() {
    stats.stringOperations.getAndIncrement();
    return delegate.none();
  }

  @Override
  public RegexFormula all() {
    stats.stringOperations.getAndIncrement();
    return delegate.all();
  }

  @Override
  public RegexFormula allChar() {
    stats.stringOperations.getAndIncrement();
    return delegate.allChar();
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    stats.stringOperations.getAndIncrement();
    return delegate.range(start, end);
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    stats.stringOperations.getAndIncrement();
    return delegate.concatRegex(parts);
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    stats.stringOperations.getAndIncrement();
    return delegate.union(regex1, regex2);
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    stats.stringOperations.getAndIncrement();
    return delegate.intersection(regex1, regex2);
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    stats.stringOperations.getAndIncrement();
    return delegate.closure(regex);
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    stats.stringOperations.getAndIncrement();
    return delegate.complement(regex);
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    stats.stringOperations.getAndIncrement();
    return delegate.difference(regex1, regex2);
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    stats.stringOperations.getAndIncrement();
    return delegate.cross(regex);
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    stats.stringOperations.getAndIncrement();
    return delegate.optional(regex);
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    stats.stringOperations.getAndIncrement();
    return delegate.times(regex, repetitions);
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    stats.stringOperations.getAndIncrement();
    return delegate.toIntegerFormula(str);
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    stats.stringOperations.getAndIncrement();
    return delegate.toStringFormula(number);
  }

  @Override
  public IntegerFormula toCodePoint(StringFormula str) {
    stats.stringOperations.getAndIncrement();
    return delegate.toCodePoint(str);
  }

  @Override
  public StringFormula fromCodePoint(IntegerFormula codepoint) {
    stats.stringOperations.getAndIncrement();
    return delegate.fromCodePoint(codepoint);
  }
}
