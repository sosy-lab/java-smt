// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import edu.stanford.CVC4.CVC4String;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class CVC5StringFormulaManager extends AbstractStringFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  CVC5StringFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    solver = pCreator.getEnv();
  }

  @Override
  protected Term makeStringImpl(String pValue) {
    // The boolean enables escape characters!
    return solver.mkString(pValue));
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Type type = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.STRING_LT, pParam2, pParam1);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.STRING_LEQ, pParam2, pParam1);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.STRING_LT, pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.STRING_LEQ, pParam1, pParam2);
  }

  @Override
  protected Term length(Term pParam) {
    return solver.mkTerm(Kind.STRING_LENGTH, pParam);
  }

  @Override
  protected Term concatImpl(List<Term> parts) {
    Preconditions.checkArgument(parts.size() > 1);
    vectorTerm vector = new vectorTerm();
    parts.forEach(vector::add);
    return solver.mkTerm(Kind.STRING_CONCAT, vector);
  }

  @Override
  protected Term prefix(Term prefix, Term str) {
    return solver.mkTerm(Kind.STRING_PREFIX, prefix, str);
  }

  @Override
  protected Term suffix(Term suffix, Term str) {
    return solver.mkTerm(Kind.STRING_SUFFIX, suffix, str);
  }

  @Override
  protected Term in(Term str, Term regex) {
    return solver.mkTerm(Kind.STRING_IN_REGEXP, str, regex);
  }

  @Override
  protected Term contains(Term str, Term part) {
    return solver.mkTerm(Kind.STRING_STRCTN, str, part);
  }

  @Override
  protected Term indexOf(Term str, Term part, Term startIndex) {
    return solver.mkTerm(Kind.STRING_STRIDOF, str, part, startIndex);
  }

  @Override
  protected Term charAt(Term str, Term index) {
    return solver.mkTerm(Kind.STRING_CHARAT, str, index);
  }

  @Override
  protected Term substring(Term str, Term index, Term length) {
    return solver.mkTerm(Kind.STRING_SUBSTR, str, index, length);
  }

  @Override
  protected Term replace(Term fullStr, Term target, Term replacement) {
    return solver.mkTerm(Kind.STRING_STRREPL, fullStr, target, replacement);
  }

  @Override
  protected Term replaceAll(Term fullStr, Term target, Term replacement) {
    return solver.mkTerm(Kind.STRING_STRREPLALL, fullStr, target, replacement);
  }

  @Override
  protected Term makeRegexImpl(String value) {
    Term str = makeStringImpl(value);
    return solver.mkTerm(Kind.STRING_TO_REGEXP, str);
  }

  @Override
  protected Term noneImpl() {
    return solver.mkTerm(Kind.REGEXP_EMPTY, new vectorTerm());
  }

  @Override
  protected Term allImpl() {
    return solver.mkTerm(Kind.REGEXP_COMPLEMENT, noneImpl());
  }

  @Override
  protected Term range(Term start, Term end) {
    return solver.mkTerm(Kind.REGEXP_RANGE, start, end);
  }

  @Override
  protected Term concatRegexImpl(List<Term> parts) {
    Preconditions.checkArgument(parts.size() > 1);
    vectorTerm vector = new vectorTerm();
    parts.forEach(vector::add);
    return solver.mkTerm(Kind.REGEXP_CONCAT, vector);
  }

  @Override
  protected Term union(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.REGEXP_UNION, pParam1, pParam2);
  }

  @Override
  protected Term intersection(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.REGEXP_INTER, pParam1, pParam2);
  }

  @Override
  protected Term closure(Term pParam) {
    return solver.mkTerm(Kind.REGEXP_STAR, pParam);
  }

  @Override
  protected Term complement(Term pParam) {
    return solver.mkTerm(Kind.REGEXP_COMPLEMENT, pParam);
  }

  @Override
  protected Term difference(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.REGEXP_DIFF, pParam1, pParam2);
  }

  @Override
  protected Term toIntegerFormula(Term pParam) {
    return solver.mkTerm(Kind.STRING_STOI, pParam);
  }

  @Override
  protected Term toStringFormula(Term pParam) {
    return solver.mkTerm(Kind.STRING_ITOS, pParam);
  }
}
