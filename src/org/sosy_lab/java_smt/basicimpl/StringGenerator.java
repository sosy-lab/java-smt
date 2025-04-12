// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

/** This class provides logging Functions for StringFormulas (for later SMTLIB2 code generating). */
public class StringGenerator {

  private StringGenerator() {}

  protected static void logMakeString(Object result, String value) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, value));
    List<Object> params = new ArrayList<>();
    params.add(value);

    // Prüfen, ob value schon als SMT-String formatiert ist (fängt und endet mit Anführungszeichen)
    boolean isQuoted = value.startsWith("\"") && value.endsWith("\"");

    String format = isQuoted ? "%s" : "\"%s\"";

    Function<List<Object>, String> functionToString =
        inputs -> String.format(format, inputs.toArray());

    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, params, functionToString, Keyword.SKIP);

    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logMakeRegex(Object result, String value) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, value));
    List<Object> params = ImmutableList.of(value);

    // Prüfen, ob der value ein echter SMT-Ausdruck ist
    boolean isExpression = value.trim().startsWith("(");

    String format = isExpression ? "(str.to_re %s)" : "(str.to_re \"%s\")";

    Function<List<Object>, String> functionToString =
        inputs -> String.format(format, inputs.toArray());

    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, params, functionToString, Keyword.SKIP);

    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logMakeVariable(Object result, String pVar) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, pVar));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.STRING));
  }

  protected static void logConcat(Object result, List<StringFormula> parts) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, parts));
    List<Object> inputParams = new ArrayList<>(parts);
    String format = "(str.++";
    for (int i = 0; i < parts.size(); i++) {
      format += " %s";
    }
    format += ")";
    logOperation(result, inputParams, format, Keyword.SKIP);
  }

  protected static void logEqual(BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "=", str1, str2);
  }

  protected static void logGreaterThan(
      BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.", str1, str2);
  }

  protected static void logGreaterOrEquals(
      BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.ge", str1, str2);
  }

  protected static void logLessThan(BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.<", str1, str2);
  }

  protected static void logLessOrEquals(
      BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.<=", str1, str2);
  }

  protected static void logPrefix(BooleanFormula result, StringFormula prefix, StringFormula str) {
    logBinaryOp(result, "str.prefixof", prefix, str);
  }

  protected static void logSuffix(BooleanFormula result, StringFormula suffix, StringFormula str) {
    logBinaryOp(result, "str.suffixof", suffix, str);
  }

  protected static void logContains(BooleanFormula result, StringFormula str, StringFormula part) {
    logBinaryOp(result, "str.contains", str, part);
  }

  protected static void logRegexRange(RegexFormula result, StringFormula start, StringFormula end) {
    List<Object> inputParams = ImmutableList.of(start, end);
    logOperation(result, inputParams, "(re.range %s %s)", Keyword.SKIP);
  }

  protected static void logRegexUnion(
      RegexFormula result, RegexFormula regex1, RegexFormula regex2) {
    List<Object> inputParams = ImmutableList.of(regex1, regex2);
    logOperation(result, inputParams, "(re.union %s %s)", Keyword.SKIP);
  }

  protected static void logRegexIntersection(
      RegexFormula result, RegexFormula regex1, RegexFormula regex2) {
    List<Object> inputParams = ImmutableList.of(regex1, regex2);
    logOperation(result, inputParams, "(re.inter %s %s)", Keyword.SKIP);
  }

  protected static void logRegexClosure(RegexFormula result, RegexFormula regex) {
    List<Object> inputParams = ImmutableList.of(regex);
    logOperation(result, inputParams, "(re.* %s)", Keyword.SKIP);
  }

  protected static void logRegexComplement(RegexFormula result, RegexFormula regex) {
    List<Object> inputParams = ImmutableList.of(regex);
    logOperation(result, inputParams, "(re.comp %s)", Keyword.SKIP);
  }

  protected static void logRegexDifference(
      RegexFormula result, RegexFormula regex1, RegexFormula regex2) {
    List<Object> inputParams = ImmutableList.of(regex1, regex2);
    logOperation(result, inputParams, "(re.diff %s %s)", Keyword.SKIP);
  }

  protected static void logIndexOf(
      IntegerFormula result, StringFormula str, StringFormula part, IntegerFormula startIndex) {
    List<Object> inputParams = ImmutableList.of(str, part, startIndex);
    logOperation(result, inputParams, "(str.indexof %s %s %s)", Keyword.SKIP);
  }

  protected static void logCharAt(Object result, StringFormula str, IntegerFormula index) {
    List<Object> inputParams = ImmutableList.of(str, index);
    logOperation(result, inputParams, "(str.at %s %s)", Keyword.SKIP);
  }

  protected static void logSubstring(
      Object result, StringFormula str, IntegerFormula index, IntegerFormula length) {
    List<Object> inputParams = ImmutableList.of(str, index, length);
    logOperation(result, inputParams, "(str.substr %s %s %s)", Keyword.SKIP);
  }

  protected static void logReplace(
      Object result, StringFormula fullStr, StringFormula target, StringFormula replacement) {
    List<Object> inputParams = ImmutableList.of(fullStr, target, replacement);
    logOperation(result, inputParams, "(str.replace %s %s %s)", Keyword.SKIP);
  }

  protected static void logReplaceAll(
      Object result, StringFormula fullStr, StringFormula target, StringFormula replacement) {
    List<Object> inputParams = ImmutableList.of(fullStr, target, replacement);
    logOperation(result, inputParams, "(str.replaceall %s %s %s)", Keyword.SKIP);
  }

  protected static void logRegexAll(RegexFormula result) {
    logOperation(result, ImmutableList.of(), "(re.all)", Keyword.SKIP);
  }

  protected static void logRegexNone(RegexFormula result) {
    logOperation(result, ImmutableList.of(), "(re.none)", Keyword.SKIP);
  }

  protected static void logRegexAllChar(RegexFormula result) {
    logOperation(result, ImmutableList.of(), "(re.allchar)", Keyword.SKIP);
  }

  protected static void logRegexConcat(RegexFormula result, List<RegexFormula> parts) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, parts));
    List<Object> inputParams = new ArrayList<>(parts);
    String format = "(re.++";
    for (int i = 0; i < parts.size(); i++) {
      format += " %s";
    }
    format += ")";
    logOperation(result, inputParams, format, Keyword.SKIP);
  }

  protected static void logRegexOptional(RegexFormula result, RegexFormula regex) {
    logOperation(result, ImmutableList.of(regex), "(re.opt %s)", Keyword.SKIP);
  }

  protected static void logRegexTimes(RegexFormula result, RegexFormula regex, int repetitions) {
    logOperation(
        result,
        ImmutableList.of(regex, repetitions),
        "((_ re.^ " + repetitions + ") %s)",
        Keyword.SKIP);
  }

  protected static void logRegexCross(RegexFormula result, RegexFormula regex) {
    logOperation(result, ImmutableList.of(regex), "(re.+ %s)", Keyword.SKIP);
  }

  protected static void logLength(IntegerFormula result, StringFormula str) {
    List<Object> inputParams = ImmutableList.of(str);
    logOperation(result, inputParams, "(str.len %s)", Keyword.SKIP);
  }

  protected static void logIn(BooleanFormula result, StringFormula str, Object regex) {
    List<Object> inputParams = ImmutableList.of(str, regex);
    logOperation(result, inputParams, "(str.in_re %s %s)", Keyword.SKIP);
  }

  protected static void logToInteger(IntegerFormula result, StringFormula str) {
    List<Object> inputParams = ImmutableList.of(str);
    logOperation(result, inputParams, "(str.to_int %s)", Keyword.SKIP);
  }

  protected static void logToString(Object result, IntegerFormula number) {
    List<Object> inputParams = ImmutableList.of(number);
    logOperation(result, inputParams, "(str.from_int %s)", Keyword.SKIP);
  }

  private static void logBinaryOp(Object result, String op, Object n1, Object n2) {
    List<Object> inputParams = ImmutableList.of(n1, n2);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logOperation(
      Object result, List<Object> params, String format, Keyword keyword) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, params, format, keyword));
    long placeholders = format.chars().filter(ch -> ch == '%').count();
    if (params.size() != placeholders) {
      throw new IllegalArgumentException(
          String.format(
              "Mismatch between placeholders (%d) and parameters (%d) for format: %s",
              placeholders, params.size(), format));
    }

    Function<List<Object>, String> functionToString =
        inputs -> String.format(format, inputs.toArray());
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, params, functionToString, keyword));
  }
}
