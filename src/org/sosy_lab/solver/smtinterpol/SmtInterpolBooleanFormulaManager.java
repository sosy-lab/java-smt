/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

class SmtInterpolBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Term, Sort, SmtInterpolEnvironment> {

  // We use the Theory directly here because the methods there perform simplifications
  // that we could not use otherwise.
  private final Theory theory;

  SmtInterpolBooleanFormulaManager(SmtInterpolFormulaCreator creator, Theory pTheory) {
    super(creator);
    theory = pTheory;
  }

  @Override
  public Term makeVariableImpl(String varName) {
    return getFormulaCreator().makeVariable(getFormulaCreator().getBoolType(), varName);
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
    assert SmtInterpolUtil.isBoolean(t1) && SmtInterpolUtil.isBoolean(t2)
        : "Cannot make equivalence of non-boolean terms:\nTerm 1:\n"
            + t1.toStringDirect()
            + "\nTerm 2:\n"
            + t2.toStringDirect();
    return theory.equals(t1, t2);
  }

  @Override
  public boolean isTrue(Term t) {
    return SmtInterpolUtil.isTrue(t);
  }

  @Override
  public boolean isFalse(Term t) {
    return SmtInterpolUtil.isFalse(t);
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
    return theory.and(SmtInterpolUtil.toTermArray(pParams));
  }

  @Override
  public Term or(Term pBits1, Term pBits2) {
    return theory.or(pBits1, pBits2);
  }

  @Override
  protected Term orImpl(Collection<Term> pParams) {
    return theory.or(SmtInterpolUtil.toTermArray(pParams));
  }

  @Override
  public Term xor(Term pBits1, Term pBits2) {
    return theory.xor(pBits1, pBits2);
  }

  @Override
  public boolean isNot(Term pBits) {
    return SmtInterpolUtil.isNot(pBits);
  }

  @Override
  public boolean isAnd(Term pBits) {
    return SmtInterpolUtil.isAnd(pBits);
  }

  @Override
  public boolean isOr(Term pBits) {
    return SmtInterpolUtil.isOr(pBits);
  }

  @Override
  public boolean isXor(Term pBits) {
    return SmtInterpolUtil.isXor(pBits);
  }

  @Override
  protected boolean isEquivalence(Term pBits) {
    return SmtInterpolUtil.isEquivalence(pBits);
  }

  @Override
  protected boolean isImplication(Term pFormula) {
    return SmtInterpolUtil.isImplication(pFormula);
  }

  @Override
  protected boolean isIfThenElse(Term pBits) {
    return SmtInterpolUtil.isIfThenElse(pBits);
  }

  private int getArity(Term pF) {
    return SmtInterpolUtil.getArity(pF);
  }

  private BooleanFormula getArg(Term pF, int index) {
    assert getFormulaCreator().getBoolType().equals(getFormulaCreator().getFormulaType(pF));
    return getFormulaCreator().encapsulateBoolean(SmtInterpolUtil.getArg(pF, index));
  }

  private List<BooleanFormula> getAllArgs(Term pF) {
    int arity = getArity(pF);
    List<BooleanFormula> args = new ArrayList<>(arity);
    for (int i = 0; i < arity; i++) {
      args.add(getArg(pF, i));
    }
    return args;
  }

  @Override
  protected <R> R visit(BooleanFormulaVisitor<R> pVisitor, Term f) {
    if (isTrue(f)) {
      assert getArity(f) == 0;
      return pVisitor.visitTrue();
    }

    if (isFalse(f)) {
      assert getArity(f) == 0;
      return pVisitor.visitFalse();
    }

    if (isNot(f)) {
      assert getArity(f) == 1;
      return pVisitor.visitNot(getArg(f, 0));
    }

    if (isAnd(f)) {
      if (getArity(f) == 0) {
        return pVisitor.visitTrue();
      } else if (getArity(f) == 1) {
        return visit(pVisitor, getArg(f, 0));
      }
      return pVisitor.visitAnd(getAllArgs(f));
    }

    if (isOr(f)) {
      if (getArity(f) == 0) {
        return pVisitor.visitFalse();
      } else if (getArity(f) == 1) {
        return pVisitor.visit(getArg(f, 0));
      }
      return pVisitor.visitOr(getAllArgs(f));
    }

    if (isEquivalence(f)) {
      assert getArity(f) == 2;
      return pVisitor.visitEquivalence(getArg(f, 0), getArg(f, 1));
    }

    if (isIfThenElse(f)) {
      assert getArity(f) == 3;
      return pVisitor.visitIfThenElse(getArg(f, 0), getArg(f, 1), getArg(f, 2));
    }

    if (SmtInterpolUtil.isAtom(f)) {
      return pVisitor.visitAtom(getFormulaCreator().encapsulateBoolean(f));
    }

    throw new UnsupportedOperationException("Unknown or unsupported boolean operator " + f);
  }
}
