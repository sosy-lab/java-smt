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
    return wrapString(makeStringImpl(value));
  }

  protected abstract TFormulaInfo makeStringImpl(String value);

  @Override
  public StringFormula makeVariable(String pVar) {
    checkVariableName(pVar);
    return wrapString(makeVariableImpl(pVar));
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar);

  @Override
  public BooleanFormula equal(StringFormula str1, StringFormula str2) {
    TFormulaInfo param1 = extractInfo(str1);
    TFormulaInfo param2 = extractInfo(str2);

    return wrapBool(equal(param1, param2));
  }

  protected abstract TFormulaInfo equal(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(StringFormula str1, StringFormula str2) {
    TFormulaInfo param1 = extractInfo(str1);
    TFormulaInfo param2 = extractInfo(str2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(StringFormula str1, StringFormula str2) {
    TFormulaInfo param1 = extractInfo(str1);
    TFormulaInfo param2 = extractInfo(str2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(StringFormula str1, StringFormula str2) {
    TFormulaInfo param1 = extractInfo(str1);
    TFormulaInfo param2 = extractInfo(str2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(StringFormula str1, StringFormula str2) {
    TFormulaInfo param1 = extractInfo(str1);
    TFormulaInfo param2 = extractInfo(str2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public NumeralFormula.IntegerFormula length(StringFormula str) {
    TFormulaInfo param = extractInfo(str);

    return getFormulaCreator().encapsulate(FormulaType.IntegerType, length(param));
  }

  protected abstract TFormulaInfo length(TFormulaInfo pParam);

  @Override
  public StringFormula concat(List<StringFormula> parts) {
    switch (parts.size()) {
      case 0:
        return makeString(""); // empty sequence
      case 1:
        return Iterables.getOnlyElement(parts);
      default:
        return wrapString(concatImpl(Lists.transform(parts, this::extractInfo)));
    }
  }

  protected abstract TFormulaInfo concatImpl(List<TFormulaInfo> parts);

  @Override
  public BooleanFormula prefix(StringFormula prefix, StringFormula str) {
    return wrapBool(prefix(extractInfo(prefix), extractInfo(str)));
  }

  protected abstract TFormulaInfo prefix(TFormulaInfo prefix, TFormulaInfo str);

  @Override
  public BooleanFormula suffix(StringFormula suffix, StringFormula str) {
    return wrapBool(suffix(extractInfo(suffix), extractInfo(str)));
  }

  protected abstract TFormulaInfo suffix(TFormulaInfo suffix, TFormulaInfo str);

  @Override
  public BooleanFormula in(StringFormula str, RegexFormula regex) {
    return wrapBool(in(extractInfo(str), extractInfo(regex)));
  }

  protected abstract TFormulaInfo in(TFormulaInfo str, TFormulaInfo regex);

  @Override
  public BooleanFormula contains(StringFormula str, StringFormula part) {
    return wrapBool(contains(extractInfo(str), extractInfo(part)));
  }

  protected abstract TFormulaInfo contains(TFormulaInfo str, TFormulaInfo part);

  @Override
  public IntegerFormula indexOf(StringFormula str, StringFormula part) {
    return getFormulaCreator()
        .encapsulate(FormulaType.IntegerType, indexOf(extractInfo(str), extractInfo(part)));
  }

  protected abstract TFormulaInfo indexOf(TFormulaInfo str, TFormulaInfo part);

  @Override
  public StringFormula charAt(StringFormula str, IntegerFormula index) {
    return wrapString(charAt(extractInfo(str), extractInfo(index)));
  }

  protected abstract TFormulaInfo charAt(TFormulaInfo str, TFormulaInfo index);

  @Override
  public StringFormula substring(StringFormula str, IntegerFormula index, IntegerFormula length) {
    return wrapString(substring(extractInfo(str), extractInfo(index), extractInfo(length)));
  }

  protected abstract TFormulaInfo substring(
      TFormulaInfo str, TFormulaInfo index, TFormulaInfo length);

  @Override
  public StringFormula replace(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    return wrapString(replace(extractInfo(fullStr), extractInfo(target), extractInfo(replacement)));
  }

  protected abstract TFormulaInfo replace(
      TFormulaInfo fullStr, TFormulaInfo target, TFormulaInfo replacement);

  @Override
  public StringFormula replaceAll(
      StringFormula fullStr, StringFormula target, StringFormula replacement) {
    return wrapString(
        replaceAll(extractInfo(fullStr), extractInfo(target), extractInfo(replacement)));
  }

  protected abstract TFormulaInfo replaceAll(
      TFormulaInfo fullStr, TFormulaInfo target, TFormulaInfo replacement);

  @Override
  public RegexFormula makeRegex(String value) {
    return wrapRegex(makeRegexImpl(value));
  }

  protected abstract TFormulaInfo makeRegexImpl(String value);

  @Override
  public RegexFormula none() {
    return wrapRegex(noneImpl());
  }

  protected abstract TFormulaInfo noneImpl();

  @Override
  public RegexFormula all() {
    return wrapRegex(allImpl());
  }

  protected abstract TFormulaInfo allImpl();

  @Override
  public RegexFormula range(StringFormula start, StringFormula end) {
    return wrapRegex(range(extractInfo(start), extractInfo(end)));
  }

  protected abstract TFormulaInfo range(TFormulaInfo start, TFormulaInfo end);

  @Override
  public RegexFormula concatRegex(List<RegexFormula> parts) {
    switch (parts.size()) {
      case 0:
        return none(); // empty sequence
      case 1:
        return Iterables.getOnlyElement(parts);
      default:
        return wrapRegex(concatRegexImpl(Lists.transform(parts, this::extractInfo)));
    }
  }

  protected abstract TFormulaInfo concatRegexImpl(List<TFormulaInfo> parts);

  @Override
  public RegexFormula union(RegexFormula regex1, RegexFormula regex2) {
    TFormulaInfo param1 = extractInfo(regex1);
    TFormulaInfo param2 = extractInfo(regex2);

    return wrapRegex(union(param1, param2));
  }

  protected abstract TFormulaInfo union(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public RegexFormula intersection(RegexFormula regex1, RegexFormula regex2) {
    TFormulaInfo param1 = extractInfo(regex1);
    TFormulaInfo param2 = extractInfo(regex2);

    return wrapRegex(union(param1, param2));
  }

  protected abstract TFormulaInfo intersection(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public RegexFormula closure(RegexFormula regex) {
    TFormulaInfo param = extractInfo(regex);

    return wrapRegex(closure(param));
  }

  protected abstract TFormulaInfo closure(TFormulaInfo pParam);

  @Override
  public RegexFormula complement(RegexFormula regex) {
    TFormulaInfo param = extractInfo(regex);

    return wrapRegex(complement(param));
  }

  protected abstract TFormulaInfo complement(TFormulaInfo pParam);

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    return intersection(regex1, complement(regex2));
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    return concat(regex, closure(regex));
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    return union(regex, makeRegex(""));
  }

  @Override
  public RegexFormula times(RegexFormula regex, int repetitions) {
    return concatRegex(Collections.nCopies(repetitions, regex));
  }
}
