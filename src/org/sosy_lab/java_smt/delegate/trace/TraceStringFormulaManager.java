// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.trace;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

public class TraceStringFormulaManager implements StringFormulaManager {

  private final StringFormulaManager delegate;
  private final TraceLogger logger;

  TraceStringFormulaManager(StringFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = checkNotNull(pDelegate);
    logger = checkNotNull(pLogger);
  }

  @Override
  public StringFormula makeString(String value) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("makeString(%s)", logger.printString(value)),
        () -> delegate.makeString(value));
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("makeVariable(%s)", logger.printString(pVar)),
        () -> delegate.makeVariable(pVar));
  }

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("equal(%s, %s)", logger.toVariable(str1), logger.toVariable(str2)),
        () -> delegate.equal(str1, str2));
  }

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("greaterThan(%s, %s)", logger.toVariable(str1), logger.toVariable(str2)),
        () -> delegate.greaterThan(str1, str2));
  }

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("greaterOrEquals(%s, %s)", logger.toVariable(str1), logger.toVariable(str2)),
        () -> delegate.greaterOrEquals(str1, str2));
  }

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("lessThan(%s, %s)", logger.toVariable(str1), logger.toVariable(str2)),
        () -> delegate.lessThan(str1, str2));
  }

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("lessOrEquals(%s, %s)", logger.toVariable(str1), logger.toVariable(str2)),
        () -> delegate.lessOrEquals(str1, str2));
  }

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("prefix(%s, %s)", logger.toVariable(prefix), logger.toVariable(str)),
        () -> delegate.prefix(prefix, str));
  }

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("suffix(%s, %s)", logger.toVariable(suffix), logger.toVariable(str)),
        () -> delegate.suffix(suffix, str));
  }

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("contains(%s, %s)", logger.toVariable(str), logger.toVariable(part)),
        () -> delegate.contains(str, part));
  }

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format(
            "indexOf(%s, %s, %s)",
            logger.toVariable(str), logger.toVariable(part), logger.toVariable(startIndex)),
        () -> delegate.indexOf(str, part, startIndex));
  }

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("charAt(%s, %s)", logger.toVariable(str), logger.toVariable(index)),
        () -> delegate.charAt(str, index));
  }

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format(
            "substring(%s, %s, %s)",
            logger.toVariable(str), logger.toVariable(index), logger.toVariable(length)),
        () -> delegate.substring(str, index, length));
  }

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format(
            "replace(%s, %s, %s)",
            logger.toVariable(fullStr), logger.toVariable(target), logger.toVariable(replacement)),
        () -> delegate.replace(fullStr, target, replacement));
  }

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format(
            "replaceAll(%s, %s, %s)",
            logger.toVariable(fullStr), logger.toVariable(target), logger.toVariable(replacement)),
        () -> delegate.replaceAll(fullStr, target, replacement));
  }

  @Override
  public IntegerFormula length(StringFormula str) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("length(%s)", logger.toVariable(str)),
        () -> delegate.length(str));
  }

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format(
            "concat(%s)",
            parts.stream().map(logger::toVariable).reduce((a, b) -> a + ", " + b).orElse("")),
        () -> delegate.concat(parts));
  }

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("in(%s, %s)", logger.toVariable(str), logger.toVariable(regex)),
        () -> delegate.in(str, regex));
  }

  @Override
  public RegexFormula makeRegex(String value) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("makeRegex(%s)", logger.printString(value)),
        () -> delegate.makeRegex(value));
  }

  @Override
  public RegexFormula none() {
    return logger.logDef("mgr.getStringFormulaManager()", "none()", delegate::none);
  }

  @Override
  public RegexFormula all() {
    return logger.logDef("mgr.getStringFormulaManager()", "all()", delegate::all);
  }

  @Override
  public RegexFormula allChar() {
    return logger.logDef("mgr.getStringFormulaManager()", "allChar()", delegate::allChar);
  }

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("range(%s, %s)", logger.toVariable(start), logger.toVariable(end)),
        () -> delegate.range(start, end));
  }

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("concatRegex(%s)", logger.toVariables(parts)),
        () -> delegate.concatRegex(parts));
  }

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("union(%s, %s)", logger.toVariable(regex1), logger.toVariable(regex2)),
        () -> delegate.union(regex1, regex2));
  }

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("intersection(%s, %s)", logger.toVariable(regex1), logger.toVariable(regex2)),
        () -> delegate.intersection(regex1, regex2));
  }

  @Override
  public RegexFormula complement(RegexFormula regex) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("complement(%s)", logger.toVariable(regex)),
        () -> delegate.complement(regex));
  }

  @Override
  public RegexFormula closure(RegexFormula regex) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("closure(%s)", logger.toVariable(regex)),
        () -> delegate.closure(regex));
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("difference(%s, %s)", logger.toVariable(regex1), logger.toVariable(regex2)),
        () -> delegate.difference(regex1, regex2));
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("cross(%s)", logger.toVariable(regex)),
        () -> delegate.cross(regex));
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("optional(%s)", logger.toVariable(regex)),
        () -> delegate.optional(regex));
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("times(%s, %d)", logger.toVariable(regex), repetitions),
        () -> delegate.times(regex, repetitions));
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("toIntegerFormula(%s)", logger.toVariable(str)),
        () -> delegate.toIntegerFormula(str));
  }

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("toStringFormula(%s)", logger.toVariable(number)),
        () -> delegate.toStringFormula(number));
  }

  @Override
  public IntegerFormula toCodePoint(StringFormula str) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("toCodePoint(%s)", logger.toVariable(str)),
        () -> delegate.toCodePoint(str));
  }

  @Override
  public StringFormula fromCodePoint(IntegerFormula codePoint) {
    return logger.logDef(
        "mgr.getStringFormulaManager()",
        String.format("fromCodePoint(%s)", logger.toVariable(codePoint)),
        () -> delegate.fromCodePoint(codePoint));
  }
}
