// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import java.util.Collections;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractStringFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements StringFormulaManager {

  protected AbstractStringFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
  }

  private StringFormula wrapString(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateString(formulaInfo);
  }

  private RegexFormula wrapRegex(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateRegex(formulaInfo);
  }

  @Override
  public StringFormula makeString(String value) {
    StringFormula result = wrapString(makeStringImpl(value));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logMakeString(result, value);
    }
    return result;
  }

  protected abstract TFormulaInfo makeStringImpl(String value);

  @Override
  public StringFormula makeVariable(String pVar) {
    checkVariableName(pVar);
    StringFormula result = wrapString(makeVariableImpl(pVar));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logMakeVariable(result, pVar);
    }
    return result;
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar);

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    BooleanFormula result = wrapBool(equal(extractInfo(str1), extractInfo(str2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logEqual(result, str1, str2);
    }
    return result;
  }

  protected abstract TFormulaInfo equal(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    BooleanFormula result = wrapBool(greaterThan(extractInfo(str1), extractInfo(str2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logGreaterThan(result, str1, str2);
    }
    return result;
  }

  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    BooleanFormula result = wrapBool(greaterOrEquals(extractInfo(str1), extractInfo(str2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logGreaterOrEquals(result, str1, str2);
    }
    return result;
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    BooleanFormula result = wrapBool(lessThan(extractInfo(str1), extractInfo(str2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logLessThan(result, str1, str2);
    }
    return result;
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    BooleanFormula result = wrapBool(lessOrEquals(extractInfo(str1), extractInfo(str2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logLessOrEquals(result, str1, str2);
    }
    return result;
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public NumeralFormula.IntegerFormula length(StringFormula str) {
    IntegerFormula result = getFormulaCreator().encapsulate(FormulaType.IntegerType, length(extractInfo(str)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logLength(result, str);
    }
    return result;
  }

  protected abstract TFormulaInfo length(TFormulaInfo pParam);

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    StringFormula result;
    switch (parts.size()) {
      case 0:
        result = makeString(""); // empty sequence
        break;
      case 1:
        result = Iterables.getOnlyElement(parts);
        break;
      default:
        result = wrapString(concatImpl(Lists.transform(parts, this::extractInfo)));
        break;
    }
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logConcat(result, parts);
    }
    return result;
  }

  protected abstract TFormulaInfo concatImpl(List<TFormulaInfo> parts);

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    BooleanFormula result = wrapBool(prefix(extractInfo(prefix), extractInfo(str)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logPrefix(result, prefix, str);
    }
    return result;
  }

  protected abstract TFormulaInfo prefix(TFormulaInfo prefix, TFormulaInfo str);

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    BooleanFormula result = wrapBool(suffix(extractInfo(suffix), extractInfo(str)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logSuffix(result, suffix, str);
    }
    return result;
  }

  protected abstract TFormulaInfo suffix(TFormulaInfo suffix, TFormulaInfo str);

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    BooleanFormula result = wrapBool(in(extractInfo(str), extractInfo(regex)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logIn(result, str, regex);
    }
    return result;
  }

  protected abstract TFormulaInfo in(TFormulaInfo str, TFormulaInfo regex);

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    BooleanFormula result = wrapBool(contains(extractInfo(str), extractInfo(part)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logContains(result, str, part);
    }
    return result;
  }

  protected abstract TFormulaInfo contains(TFormulaInfo str, TFormulaInfo part);

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part, IntegerFormula startIndex) {
    IntegerFormula result = getFormulaCreator()
        .encapsulate(
            FormulaType.IntegerType,
            indexOf(extractInfo(str), extractInfo(part), extractInfo(startIndex)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logIndexOf(result, str, part, startIndex);
    }
    return result;
  }

  protected abstract TFormulaInfo indexOf(
      TFormulaInfo str, TFormulaInfo part, TFormulaInfo startIndex);

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    StringFormula result = wrapString(charAt(extractInfo(str), extractInfo(index)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logCharAt(result, str, index);
    }
    return result;
  }

  protected abstract TFormulaInfo charAt(TFormulaInfo str, TFormulaInfo index);

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    StringFormula result = wrapString(substring(extractInfo(str), extractInfo(index), extractInfo(length)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logSubstring(result, str, index, length);
    }
    return result;
  }


  protected abstract TFormulaInfo substring(
      TFormulaInfo str, TFormulaInfo index, TFormulaInfo length);

  @Override
  public StringFormula replace(StringFormula fullStr, StringFormula target, StringFormula replacement) {
    StringFormula result = wrapString(replace(extractInfo(fullStr), extractInfo(target), extractInfo(replacement)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logReplace(result, fullStr, target, replacement);
    }
    return result;
  }

  protected abstract TFormulaInfo replace(
      TFormulaInfo fullStr, TFormulaInfo target, TFormulaInfo replacement);

  @Override
  public StringFormula replaceAll(StringFormula fullStr, StringFormula target, StringFormula replacement) {
    StringFormula result = wrapString(
        replaceAll(extractInfo(fullStr), extractInfo(target), extractInfo(replacement)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logReplaceAll(result, fullStr, target, replacement);
    }
    return result;
  }

  protected abstract TFormulaInfo replaceAll(
      TFormulaInfo fullStr, TFormulaInfo target, TFormulaInfo replacement);

  @Override
  public RegexFormula makeRegex(String value) {
    RegexFormula result = wrapRegex(makeRegexImpl(value));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logMakeRegex(result, value);
    }
    return result;
  }

  protected abstract TFormulaInfo makeRegexImpl(String value);

  @Override
  public RegexFormula none() {
    RegexFormula result = wrapRegex(noneImpl());
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexNone(result);
    }
    return result;
  }

  protected abstract TFormulaInfo noneImpl();

  @Override
  public RegexFormula all() {
    RegexFormula result = wrapRegex(allImpl());
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexAll(result);
    }
    return result;
  }

  protected abstract TFormulaInfo allImpl();

  @Override
  public RegexFormula allChar() {
    RegexFormula result = wrapRegex(allCharImpl());
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexAllChar(result);
    }
    return result;
  }

  protected abstract TFormulaInfo allCharImpl();

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    RegexFormula result = wrapRegex(range(extractInfo(start), extractInfo(end)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexRange(result, start, end);
    }
    return result;
  }

  protected abstract TFormulaInfo range(TFormulaInfo start, TFormulaInfo end);

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    RegexFormula result;
    switch (parts.size()) {
      case 0:
        result = none(); // empty sequence
        break;
      case 1:
        result = Iterables.getOnlyElement(parts);
        break;
      default:
        result = wrapRegex(concatRegexImpl(Lists.transform(parts, this::extractInfo)));
        break;
    }
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexConcat(result, parts);
    }
    return result;
  }

  protected abstract TFormulaInfo concatRegexImpl(List<TFormulaInfo> parts);

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    RegexFormula result = wrapRegex(union(extractInfo(regex1), extractInfo(regex2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexUnion(result, regex1, regex2);
    }
    return result;
  }

  protected abstract TFormulaInfo union(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    RegexFormula result = wrapRegex(intersection(extractInfo(regex1), extractInfo(regex2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexIntersection(result, regex1, regex2);
    }
    return result;
  }

  protected abstract TFormulaInfo intersection(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public RegexFormula closure(RegexFormula regex) {
    RegexFormula result = wrapRegex(closure(extractInfo(regex)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexClosure(result, regex);
    }
    return result;
  }

  protected abstract TFormulaInfo closure(TFormulaInfo pParam);

  @Override
  public RegexFormula complement(RegexFormula regex) {
    RegexFormula result = wrapRegex(complement(extractInfo(regex)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexComplement(result, regex);
    }
    return result;
  }

  protected abstract TFormulaInfo complement(TFormulaInfo pParam);

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    RegexFormula result = wrapRegex(difference(extractInfo(regex1), extractInfo(regex2)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexDifference(result, regex1, regex2);
    }
    return result;
  }

  protected TFormulaInfo difference(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    return intersection(pParam1, complement(pParam2));
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    RegexFormula result = concat(regex, closure(regex));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexCross(result, regex);
    }
    return result;
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    RegexFormula result = union(regex, makeRegex(""));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexOptional(result, regex);
    }
    return result;
  }
  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    RegexFormula result = concatRegex(Collections.nCopies(repetitions, regex));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logRegexTimes(result, regex, repetitions);
    }
    return result;
  }

  @Override
  public IntegerFormula toIntegerFormula(StringFormula str) {
    IntegerFormula result = getFormulaCreator()
        .encapsulate(FormulaType.IntegerType, toIntegerFormula(extractInfo(str)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logToInteger(result, str);
    }
    return result;
  }

  protected abstract TFormulaInfo toIntegerFormula(TFormulaInfo pParam);

  @Override
  public StringFormula toStringFormula(IntegerFormula number) {
    StringFormula result = wrapString(toStringFormula(extractInfo(number)));
    if (Generator.isLoggingEnabled()) {
      StringGenerator.logToString(result, number);
    }
    return result;
  }

  protected abstract TFormulaInfo toStringFormula(TFormulaInfo pParam);
}
