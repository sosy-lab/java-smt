/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package org.sosy_lab.java_smt.basicimpl;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class StringGenerator {

  private StringGenerator() {}

  protected static void logMakeString(Object result, String value) {
    List<Object> params = new ArrayList<>();
    params.add(value);
    String format = "\"%s\"";
    Function<List<Object>, String> functionToString =
        inputs -> String.format(format, inputs.toArray());
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, params, functionToString, Keyword.SKIP);
    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logMakeVariable(Object result, String pVar) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.STRING));
  }

  protected static void logConcat(Object result, List<StringFormula> parts) {
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
    logBinaryOp(result, "str.gt", str1, str2);
  }

  protected static void logGreaterOrEquals(
      BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.ge", str1, str2);
  }

  protected static void logLessThan(BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.lt", str1, str2);
  }

  protected static void logLessOrEquals(
      BooleanFormula result, StringFormula str1, StringFormula str2) {
    logBinaryOp(result, "str.le", str1, str2);
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
    List<Object> inputParams = List.of(start, end);
    logOperation(result, inputParams, "(str.range %s %s)", Keyword.SKIP);
  }

  protected static void logRegexUnion(
      RegexFormula result, RegexFormula regex1, RegexFormula regex2) {
    List<Object> inputParams = List.of(regex1, regex2);
    logOperation(result, inputParams, "(re.union %s %s)", Keyword.SKIP);
  }

  protected static void logRegexIntersection(
      RegexFormula result, RegexFormula regex1, RegexFormula regex2) {
    List<Object> inputParams = List.of(regex1, regex2);
    logOperation(result, inputParams, "(re.inter %s %s)", Keyword.SKIP);
  }

  protected static void logRegexClosure(RegexFormula result, RegexFormula regex) {
    List<Object> inputParams = List.of(regex);
    logOperation(result, inputParams, "(re.* %s)", Keyword.SKIP);
  }

  protected static void logRegexComplement(RegexFormula result, RegexFormula regex) {
    List<Object> inputParams = List.of(regex);
    logOperation(result, inputParams, "(re.complement %s)", Keyword.SKIP);
  }

  protected static void logRegexDifference(
      RegexFormula result, RegexFormula regex1, RegexFormula regex2) {
    List<Object> inputParams = List.of(regex1, regex2);
    logOperation(result, inputParams, "(re.diff %s %s)", Keyword.SKIP);
  }

  protected static void logIndexOf(
      IntegerFormula result, StringFormula str, StringFormula part, IntegerFormula startIndex) {
    List<Object> inputParams = List.of(str, part, startIndex);
    logOperation(result, inputParams, "(str.indexof %s %s %s)", Keyword.SKIP);
  }

  protected static void logCharAt(Object result, StringFormula str, IntegerFormula index) {
    List<Object> inputParams = List.of(str, index);
    logOperation(result, inputParams, "(str.at %s %s)", Keyword.SKIP);
  }

  protected static void logSubstring(
      Object result, StringFormula str, IntegerFormula index, IntegerFormula length) {
    List<Object> inputParams = List.of(str, index, length);
    logOperation(result, inputParams, "(str.substr %s %s %s)", Keyword.SKIP);
  }

  protected static void logReplace(
      Object result, StringFormula fullStr, StringFormula target, StringFormula replacement) {
    List<Object> inputParams = List.of(fullStr, target, replacement);
    logOperation(result, inputParams, "(str.replace %s %s %s)", Keyword.SKIP);
  }

  protected static void logReplaceAll(
      Object result, StringFormula fullStr, StringFormula target, StringFormula replacement) {
    List<Object> inputParams = List.of(fullStr, target, replacement);
    logOperation(result, inputParams, "(str.replaceall %s %s %s)", Keyword.SKIP);
  }

  protected static void logMakeRegex(RegexFormula result, String value) {
    List<Object> inputParams = List.of(value);
    logOperation(result, inputParams, "(re.from_str \"%s\")", Keyword.SKIP);
  }

  protected static void logRegexAll(RegexFormula result) {
    logOperation(result, List.of(), "(re.all)", Keyword.SKIP);
  }

  protected static void logRegexNone(RegexFormula result) {
    logOperation(result, List.of(), "(re.none)", Keyword.SKIP);
  }

  protected static void logRegexAllChar(RegexFormula result) {
    logOperation(result, List.of(), "(re.allchar)", Keyword.SKIP);
  }

  protected static void logRegexConcat(RegexFormula result, List<RegexFormula> parts) {
    logOperation(result, new ArrayList<>(parts), "(re.++ %s %s)", Keyword.SKIP);
  }

  protected static void logRegexOptional(RegexFormula result, RegexFormula regex) {
    logOperation(result, List.of(regex), "(re.opt %s)", Keyword.SKIP);
  }

  protected static void logRegexTimes(RegexFormula result, RegexFormula regex, int repetitions) {
    logOperation(result, List.of(regex, repetitions), "(re.tms %s %d)", Keyword.SKIP);
  }

  protected static void logRegexCross(RegexFormula result, RegexFormula regex) {
    logOperation(result, List.of(regex), "(re.cross %s)", Keyword.SKIP);
  }

  protected static void logLength(IntegerFormula result, StringFormula str) {
    List<Object> inputParams = List.of(str);
    logOperation(result, inputParams, "(str.len %s)", Keyword.SKIP);
  }

  protected static void logIn(BooleanFormula result, StringFormula str, Object regex) {
    List<Object> inputParams = List.of(str, regex);
    logOperation(result, inputParams, "(str.in_re %s %s)", Keyword.SKIP);
  }

  protected static void logToInteger(IntegerFormula result, StringFormula str) {
    List<Object> inputParams = List.of(str);
    logOperation(result, inputParams, "(str.to_int %s)", Keyword.SKIP);
  }

  protected static void logToString(Object result, IntegerFormula number) {
    List<Object> inputParams = List.of(number);
    logOperation(result, inputParams, "(int.to_str %s)", Keyword.SKIP);
  }

  private static void logBinaryOp(Object result, String op, Object n1, Object n2) {
    List<Object> inputParams = List.of(n1, n2);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logOperation(
      Object result, List<Object> params, String format, Keyword keyword) {
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
