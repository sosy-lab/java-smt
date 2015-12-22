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

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.solver.smtinterpol.SmtInterpolUtil.toTermArray;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractUnsafeFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

class SmtInterpolUnsafeFormulaManager
    extends AbstractUnsafeFormulaManager<Term, Sort, SmtInterpolEnvironment> {

  private final SmtInterpolFormulaCreator formulaCreator;

  SmtInterpolUnsafeFormulaManager(SmtInterpolFormulaCreator pCreator) {
    super(pCreator);
    formulaCreator = pCreator;
  }

  /** ApplicationTerms can be wrapped with "|".
   * This function removes those chars. */
  static String dequote(String s) {
    return s.replace("|", "");
  }

  @Override
  public boolean isAtom(Term t) {
    return SmtInterpolUtil.isAtom(t);
  }

  @Override
  public int getArity(Term pT) {
    assert !(pT instanceof LetTerm)
        : "Formulas used by JavaSMT are expected to not have LetTerms."
            + " Check how this formula was created: "
            + pT;
    return SmtInterpolUtil.getArity(pT);
  }

  @Override
  public Term getArg(Term pT, int pN) {
    Preconditions.checkState(pT instanceof ApplicationTerm);
    return ((ApplicationTerm) pT).getParameters()[pN];
  }

  @Override
  public boolean isVariable(Term pT) {
    return SmtInterpolUtil.isVariable(pT);
  }

  @Override
  public boolean isUF(Term t) {
    return SmtInterpolUtil.isUIF(t);
  }

  @Override
  public String getName(Term t) {
    if (isUF(t)) {
      return ((ApplicationTerm) t).getFunction().getName();
    } else {
      return dequote(t.toString());
    }
  }

  @Override
  public Term replaceArgs(Term pT, List<Term> newArgs) {
    return SmtInterpolUtil.replaceArgs(
        getFormulaCreator().getEnv(), pT, SmtInterpolUtil.toTermArray(newArgs));
  }

  @Override
  protected Term replaceArgsAndName(Term t, String pNewName, List<Term> pNewArgs) {
    if (isVariable(t)) {
      checkArgument(pNewArgs.isEmpty());
      return getFormulaCreator().makeVariable(t.getSort(), pNewName);

    } else if (isUF(t)) {
      ApplicationTerm at = (ApplicationTerm) t;
      Term[] args = at.getParameters();
      Sort[] sorts = new Sort[args.length];
      for (int i = 0; i < sorts.length; i++) {
        sorts[i] = args[i].getSort();
      }
      getFormulaCreator().getEnv().declareFun(pNewName, sorts, t.getSort());
      return createUIFCallImpl(pNewName, toTermArray(pNewArgs));
    } else {
      throw new IllegalArgumentException("The Term " + t + " has no name!");
    }
  }

  @Override
  public Formula substitute(Formula pF, Map<Formula, Formula> pFromToMapping) {
    return substituteUsingMap(pF, pFromToMapping);
  }

  @Override
  protected List<Term> splitNumeralEqualityIfPossible(Term pF) {
    if (SmtInterpolUtil.isFunction(pF, "=") && SmtInterpolUtil.getArity(pF) == 2) {
      Term arg0 = SmtInterpolUtil.getArg(pF, 0);
      Term arg1 = SmtInterpolUtil.getArg(pF, 1);
      assert arg0 != null && arg1 != null;
      assert arg0.getSort().equals(arg1.getSort());
      if (!SmtInterpolUtil.isBoolean(arg0)) {
        return ImmutableList.of(
            getFormulaCreator().getEnv().term("<=", arg0, arg1),
            getFormulaCreator().getEnv().term("<=", arg1, arg0));
      }
    }
    return ImmutableList.of(pF);
  }

  Term createUIFCallImpl(String funcDecl, Term[] args) {
    Term ufc = getFormulaCreator().getEnv().term(funcDecl, args);
    assert SmtInterpolUtil.isUIF(ufc);
    return ufc;
  }

  @Override
  public boolean isNumber(Term pT) {
    return SmtInterpolUtil.isNumber(pT);
  }

  @Override
  protected boolean isQuantification(Term pT) {
    return false;
  }

  @Override
  protected Term getQuantifiedBody(Term pT) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected Term replaceQuantifiedBody(Term pF, Term pBody) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected boolean isFreeVariable(Term pT) {
    return isVariable(pT);
  }

  @Override
  protected boolean isBoundVariable(Term pT) {
    return false;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Term input) {
    if (isNumber(input)) {
      return visitor.visitNumeral(input.toString(), formulaCreator.getFormulaType(input));
    } else if (isQuantification(input)) {
      // TODO: quantifier support.
      throw new UnsupportedOperationException("Quantifiers " + "for Princess not supported");
    } else if (isBoundVariable(input)) {
      return visitor.visitBoundVariable(getName(input), formulaCreator.getFormulaType(input));
    } else if (isVariable(input)) {
      return visitor.visitFreeVariable(getName(input), formulaCreator.getFormulaType(input));
    } else {
      int arity = getArity(input);
      String name = getName(input);
      final FormulaType<?> type = formulaCreator.getFormulaType(input);
      List<Formula> args = new ArrayList<>(arity);
      List<FormulaType<?>> formulaTypes = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        Term arg = getArg(input, i);
        FormulaType<?> argumentType = formulaCreator.getFormulaType(arg);
        formulaTypes.add(argumentType);
        args.add(formulaCreator.encapsulate(argumentType, arg));
      }
      if (isUF(input)) {
        // Special casing for UFs.
        return visitor.visitUF(
            name, formulaCreator.createUfDeclaration(type, input.getSort(), formulaTypes), args);
      } else {

        // Any function application.
        Function<List<Formula>, Formula> constructor =
            new Function<List<Formula>, Formula>() {
              @Override
              public Formula apply(List<Formula> formulas) {
                return replaceArgs(formulaCreator.encapsulate(type, input), formulas);
              }
            };
        return visitor.visitFunction(name, args, type, constructor);
      }
    }
  }
}
