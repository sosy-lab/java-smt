// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import java.util.Collection;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class SmtInterpolBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> {

  // We use the Theory directly here because the methods there perform simplifications
  // that we could not use otherwise.
  private final Theory theory;

  SmtInterpolBooleanFormulaManager(SmtInterpolFormulaCreator creator, Theory pTheory) {
    super(creator);
    theory = pTheory;
  }

  @Override
  public Term makeVariableImpl(String varName) {
    return formulaCreator.makeVariable(formulaCreator.getBoolType(), varName);
  }

  @Override
  public Term makeBooleanImpl(boolean pValue) {
    Term t;
    if (pValue) {
      t = theory.mTrue;
    } else {
      t = theory.mFalse;
    }
    return t;
  }

  @Override
  public Term equivalence(Term t1, Term t2) {
    assert t1.getTheory().getBooleanSort() == t1.getSort()
            && t2.getTheory().getBooleanSort() == t2.getSort()
        : "Cannot make equivalence of non-boolean terms:\nTerm 1:\n"
            + t1.toStringDirect()
            + "\nTerm 2:\n"
            + t2.toStringDirect();
    return theory.equals(t1, t2);
  }

  @Override
  public boolean isTrue(Term t) {
    return t.getTheory().mTrue == t;
  }

  @Override
  public boolean isFalse(Term t) {
    return t.getTheory().mFalse == t;
  }

  @Override
  public Term ifThenElse(Term condition, Term t1, Term t2) {
    return theory.ifthenelse(condition, t1, t2);
  }

  @Override
  public Term not(Term pBits) {
    return theory.not(pBits);
  }

  @Override
  public Term and(Term pBits1, Term pBits2) {
    return theory.and(pBits1, pBits2);
  }

  @Override
  protected Term andImpl(Collection<Term> pParams) {
    // SMTInterpol does all simplifications itself
    return theory.and(pParams.toArray(new Term[0]));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  public Term or(Term pBits1, Term pBits2) {
    return theory.or(pBits1, pBits2);
  }

  @Override
  protected Term orImpl(Collection<Term> pParams) {
    // SMTInterpol does all simplifications itself
    return theory.or(pParams.toArray(new Term[0]));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  public Term xor(Term pBits1, Term pBits2) {
    return theory.xor(pBits1, pBits2);
  }
}
