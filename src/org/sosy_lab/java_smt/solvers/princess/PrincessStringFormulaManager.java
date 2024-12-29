// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toITermSeq;

import ap.parser.IAtom;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.ITerm;
import ap.types.Sort;
import com.google.common.collect.ImmutableList;
import java.util.List;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

public class PrincessStringFormulaManager
    extends AbstractStringFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  PrincessStringFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected IExpression makeStringImpl(String value) {
    value = unescapeUnicodeForSmtlib(value);
    checkArgument(!containsSurrogatePair(value), "Princess does not support surrogate pairs.");
    return PrincessEnvironment.stringTheory.string2Term(value);
  }

  /** returns whether any character of the string is part of a surrogate pair. */
  private static boolean containsSurrogatePair(String str) {
    return str.codePoints().anyMatch(Character::isSupplementaryCodePoint);
  }

  @Override
  protected IExpression makeVariableImpl(String pVar) {
    Sort t = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(t, pVar);
  }

  @Override
  protected IFormula equal(IExpression pParam1, IExpression pParam2) {
    return ((ITerm) pParam1).$eq$eq$eq((ITerm) pParam2);
  }

  @Override
  protected IFormula greaterThan(IExpression pParam1, IExpression pParam2) {
    // just reverse the order
    return lessThan(pParam2, pParam1);
  }

  @Override
  protected IFormula lessOrEquals(IExpression pParam1, IExpression pParam2) {
    return new IAtom(PrincessEnvironment.stringTheory.str_$less$eq(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected IFormula greaterOrEquals(IExpression pParam1, IExpression pParam2) {
    // just reverse the order
    return lessOrEquals(pParam2, pParam1);
  }

  @Override
  protected IFormula lessThan(IExpression pParam1, IExpression pParam2) {
    return new IAtom(PrincessEnvironment.stringTheory.str_$less(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm length(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_len(), toITermSeq(pParam));
  }

  @Override
  protected ITerm concatImpl(List<IExpression> parts) {
    ITerm result = (ITerm) makeStringImpl("");
    for (IExpression expr : parts) {
      result =
          new IFunApp(
              PrincessEnvironment.stringTheory.str_$plus$plus(),
              PrincessEnvironment.toSeq(ImmutableList.of(result, (ITerm) expr)));
    }
    return result;
  }

  @Override
  protected IFormula prefix(IExpression prefix, IExpression str) {
    return new IAtom(PrincessEnvironment.stringTheory.str_prefixof(), toITermSeq(prefix, str));
  }

  @Override
  protected IFormula suffix(IExpression suffix, IExpression str) {
    return new IAtom(PrincessEnvironment.stringTheory.str_suffixof(), toITermSeq(suffix, str));
  }

  @Override
  protected IFormula in(IExpression str, IExpression regex) {
    return new IAtom(PrincessEnvironment.stringTheory.str_in_re(), toITermSeq(str, regex));
  }

  @Override
  protected IFormula contains(IExpression str, IExpression part) {
    return new IAtom(PrincessEnvironment.stringTheory.str_contains(), toITermSeq(str, part));
  }

  @Override
  protected ITerm indexOf(IExpression str, IExpression part, IExpression startIndex) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_indexof(), toITermSeq(str, part, startIndex));
  }

  @Override
  protected ITerm charAt(IExpression str, IExpression index) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_at(), toITermSeq(str, index));
  }

  @Override
  protected ITerm substring(IExpression str, IExpression index, IExpression length) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_substr(), toITermSeq(str, index, length));
  }

  @Override
  protected ITerm replace(IExpression fullStr, IExpression target, IExpression replacement) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_replace(), toITermSeq(fullStr, target, replacement));
  }

  @Override
  protected ITerm replaceAll(IExpression fullStr, IExpression target, IExpression replacement) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_replaceall(),
        toITermSeq(fullStr, target, replacement));
  }

  @Override
  protected ITerm makeRegexImpl(String value) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_to_re(), toITermSeq(makeStringImpl(value)));
  }

  @Override
  protected ITerm noneImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_none(), toITermSeq());
  }

  @Override
  protected ITerm allImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_all(), toITermSeq());
  }

  @Override
  protected IExpression allCharImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_allchar(), toITermSeq());
  }

  @Override
  protected ITerm range(IExpression start, IExpression end) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_range(), toITermSeq());
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    return wrapRegex(
        new IFunApp(PrincessEnvironment.stringTheory.re_$plus(), toITermSeq(extractInfo(regex))));
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    return wrapRegex(
        new IFunApp(PrincessEnvironment.stringTheory.re_opt(), toITermSeq(extractInfo(regex))));
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    return wrapRegex(
        new IFunApp(
            PrincessEnvironment.stringTheory.re_diff(),
            toITermSeq(extractInfo(regex1), extractInfo(regex2))));
  }

  @Override
  protected ITerm concatRegexImpl(List<IExpression> parts) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_$plus$plus(), toITermSeq(parts));
  }

  @Override
  protected ITerm union(IExpression pParam1, IExpression pParam2) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_union(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm intersection(IExpression pParam1, IExpression pParam2) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_inter(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm closure(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_$times(), toITermSeq(pParam));
  }

  @Override
  protected ITerm complement(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_comp(), toITermSeq(pParam));
  }

  @Override
  protected ITerm toIntegerFormula(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_to_int(), toITermSeq(pParam));
  }

  @Override
  protected ITerm toStringFormula(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.int_to_str(), toITermSeq(pParam));
  }

  @Override
  protected IExpression toCodePoint(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_to_code(), toITermSeq(pParam));
  }

  @Override
  protected IExpression fromCodePoint(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_from_code(), toITermSeq(pParam));
  }
}
