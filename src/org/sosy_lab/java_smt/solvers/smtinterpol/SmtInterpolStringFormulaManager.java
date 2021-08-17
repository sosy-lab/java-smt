// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class SmtInterpolStringFormulaManager
    extends AbstractStringFormulaManager<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> {

  // We use the Theory directly here because the methods there perform simplifications
  // that we could not use otherwise.
  private final Theory theory;

  SmtInterpolStringFormulaManager(SmtInterpolFormulaCreator creator, Theory pTheory) {
    super(creator);
    theory = pTheory;
  }

  @Override
  public Term makeStringImpl(String pValue) {
    return theory.string(new QuotedObject(pValue));
  }

  @Override
  public Term makeVariableImpl(String varName) {
    return formulaCreator.makeVariable(formulaCreator.getStringType(), varName);
  }

  @Override
  public Term equal(Term t1, Term t2) {
    assert t1.getTheory().getStringSort() == t1.getSort()
        && t2.getTheory().getStringSort() == t2.getSort()
        : "Cannot make equality of non-string terms:\nTerm 1:\n"
        + t1.toStringDirect()
        + "\nTerm 2:\n"
        + t2.toStringDirect();
    return theory.equals(t1, t2);
  }
}