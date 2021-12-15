// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.INot;
import ap.parser.ITerm;
import ap.types.Sort;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;
import scala.collection.immutable.Seq;

public class PrincessStringFormulaManager
    extends AbstractStringFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  PrincessStringFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  static Seq<ITerm> toSeq(List<IExpression> exprs) {
    ArrayList<ITerm> result = new ArrayList<ITerm>();
    for (IExpression expr : exprs) result.add((ITerm) expr);
    return PrincessEnvironment.toSeq(result);
  }

  static Seq<ITerm> toSeq(IExpression... exprs) {
    return toSeq(Arrays.asList(exprs));
  }

  @Override
  protected IExpression makeStringImpl(String value) {
    return PrincessEnvironment.stringTheory.string2Term(value);
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
    IFormula leq = greaterOrEquals(pParam1, pParam2);
    IFormula eq = equal(pParam1, pParam2);
    return new IBinFormula(IBinJunctor.And(), leq, new INot(eq));
  }

  @Override
  protected IFormula lessOrEquals(IExpression pParam1, IExpression pParam2) {
    return new IAtom(PrincessEnvironment.stringTheory.str_$less$eq(), toSeq(pParam1, pParam2));
  }

  @Override
  protected IFormula greaterOrEquals(IExpression pParam1, IExpression pParam2) {
    // just reverse the order
    return lessOrEquals(pParam2, pParam1);
  }

  @Override
  protected IFormula lessThan(IExpression pParam1, IExpression pParam2) {
    IFormula leq = lessOrEquals(pParam1, pParam2);
    IFormula eq = equal(pParam1, pParam2);
    return new IBinFormula(IBinJunctor.And(), leq, new INot(eq));
  }

  @Override
  protected ITerm length(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_len(), toSeq(pParam));
  }

  @Override
  protected ITerm concatImpl(List<IExpression> parts) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_$plus$plus(), toSeq(parts));
  }

  @Override
  protected IFormula prefix(IExpression prefix, IExpression str) {
    return new IAtom(PrincessEnvironment.stringTheory.str_prefixof(), toSeq(prefix, str));
  }

  @Override
  protected IFormula suffix(IExpression suffix, IExpression str) {
    return new IAtom(PrincessEnvironment.stringTheory.str_suffixof(), toSeq(suffix, str));
  }

  @Override
  protected IFormula in(IExpression str, IExpression regex) {
    return new IAtom(PrincessEnvironment.stringTheory.str_in_re(), toSeq(str, regex));
  }

  @Override
  protected IFormula contains(IExpression str, IExpression part) {
    return new IAtom(PrincessEnvironment.stringTheory.str_contains(), toSeq(str, part));
  }

  @Override
  protected ITerm indexOf(IExpression str, IExpression part, IExpression startIndex) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_indexof(), toSeq(str, part, startIndex));
  }

  @Override
  protected ITerm charAt(IExpression str, IExpression index) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_char(), toSeq(str, index));
  }

  @Override
  protected ITerm substring(IExpression str, IExpression index, IExpression length) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_substr(), toSeq(str, index, length));
  }

  @Override
  protected ITerm replace(IExpression fullStr, IExpression target, IExpression replacement) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_replace(), toSeq(fullStr, target, replacement));
  }

  @Override
  protected ITerm replaceAll(IExpression fullStr, IExpression target, IExpression replacement) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_replaceall(), toSeq(fullStr, target, replacement));
  }

  @Override
  protected ITerm makeRegexImpl(String value) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_to_re(), toSeq(makeStringImpl(value)));
  }

  @Override
  protected ITerm noneImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_none(), toSeq());
  }

  @Override
  protected ITerm allImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_all(), toSeq());
  }

  @Override
  protected ITerm range(IExpression start, IExpression end) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_range(), toSeq());
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    return wrapRegex(
        new IFunApp(PrincessEnvironment.stringTheory.re_$plus(), toSeq(extractInfo(regex))));
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    return wrapRegex(
        new IFunApp(PrincessEnvironment.stringTheory.re_opt(), toSeq(extractInfo(regex))));
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    return wrapRegex(
        new IFunApp(
            PrincessEnvironment.stringTheory.re_diff(),
            toSeq(extractInfo(regex1), extractInfo(regex2))));
  }

  @Override
  protected ITerm concatRegexImpl(List<IExpression> parts) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_$plus$plus(), toSeq(parts));
  }

  @Override
  protected ITerm union(IExpression pParam1, IExpression pParam2) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_union(), toSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm intersection(IExpression pParam1, IExpression pParam2) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_inter(), toSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm closure(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_$times(), toSeq(pParam));
  }

  @Override
  protected ITerm complement(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_comp(), toSeq(pParam));
  }

  @Override
  protected ITerm toIntegerFormula(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_to_int(), toSeq(pParam));
  }

  @Override
  protected ITerm toStringFormula(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.int_to_str(), toSeq(pParam));
  }
}
