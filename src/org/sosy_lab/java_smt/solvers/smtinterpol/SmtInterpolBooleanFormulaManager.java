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
package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import java.util.Collection;
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
    return theory.and(pParams.toArray(new Term[pParams.size()]));
  }

  @Override
  public Term or(Term pBits1, Term pBits2) {
    return theory.or(pBits1, pBits2);
  }

  @Override
  protected Term orImpl(Collection<Term> pParams) {
    return theory.or(pParams.toArray(new Term[pParams.size()]));
  }

  @Override
  public Term xor(Term pBits1, Term pBits2) {
    return theory.xor(pBits1, pBits2);
  }
}
