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
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.FuncDeclKind;
import org.sosy_lab.solver.basicimpl.AbstractUnsafeFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.List;
import java.util.Map;

class SmtInterpolUnsafeFormulaManager
    extends AbstractUnsafeFormulaManager<Term, Sort, SmtInterpolEnvironment> {

  private final SmtInterpolFormulaCreator formulaCreator;
  private final Theory theory;

  SmtInterpolUnsafeFormulaManager(SmtInterpolFormulaCreator pCreator, Theory pTheory) {
    super(pCreator);
    formulaCreator = pCreator;
    theory = pTheory;
  }

  /**
   * ApplicationTerms can be wrapped with "|".
   * This function removes those chars.
   **/
  static String dequote(String s) {
    int l = s.length();
    if (s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
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
  public Term replaceArgs(Term pT, List<Term> newArgs) {
    return SmtInterpolUtil.replaceArgs(
        getFormulaCreator().getEnv(), pT, SmtInterpolUtil.toTermArray(newArgs));
  }

  @Override
  protected Term replaceArgsAndName(Term t, String pNewName, List<Term> pNewArgs) {
    if (isVariable(t)) {
      checkArgument(pNewArgs.isEmpty());
      return getFormulaCreator().makeVariable(t.getSort(), pNewName);

    } else if (SmtInterpolUtil.isUIF(t)) {
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
  public <R> R visit(FormulaVisitor<R> visitor, Formula f, final Term input) {
    checkArgument(
        input.getTheory().equals(theory),
        "Given term belongs to a different instance of SMTInterpol: %s",
        input);
    final FormulaType<?> formulaType = formulaCreator.getFormulaType(input);

    if (SmtInterpolUtil.isNumber(input)) {
      final Object value = SmtInterpolUtil.toNumber(input);
      assert value instanceof Number;
      return visitor.visitConstant(f, value);

    } else if (input instanceof ApplicationTerm) {
      final ApplicationTerm app = (ApplicationTerm) input;
      final int arity = app.getParameters().length;
      final FunctionSymbol func = app.getFunction();

      if (arity == 0) {
        if (app.equals(theory.mTrue)) {
          return visitor.visitConstant(f, Boolean.TRUE);
        } else if (app.equals(theory.mFalse)) {
          return visitor.visitConstant(f, Boolean.FALSE);
        } else if (func.getDefinition() == null) {
          return visitor.visitFreeVariable(f, dequote(input.toString()));
        } else {
          throw new UnsupportedOperationException("Unexpected nullary function " + input);
        }

      } else {
        final String name = func.getName();
        final List<Formula> args = formulaCreator.encapsulate(app.getParameters());

        // Any function application.
        Function<List<Formula>, Formula> constructor =
            new Function<List<Formula>, Formula>() {
              @Override
              public Formula apply(List<Formula> formulas) {
                return replaceArgs(formulaCreator.encapsulate(formulaType, input), formulas);
              }
            };
        return visitor.visitFuncApp(
            f, args, FuncDecl.of(name, getDeclarationKind(app)), constructor);
      }

    } else {
      // TODO: support for quantifiers and bound variables

      throw new UnsupportedOperationException(
          String.format(
              "Unexpected SMTInterpol formula of type %s: %s",
              input.getClass().getSimpleName(),
              input));
    }
  }

  private FuncDeclKind getDeclarationKind(ApplicationTerm input) {
    FunctionSymbol symbol = input.getFunction();
    Theory t = input.getTheory();
    if (SmtInterpolUtil.isUIF(input)) {
      return FuncDeclKind.UF;
    } else if (symbol == t.mAnd) {
      return FuncDeclKind.AND;
    } else if (symbol == t.mOr) {
      return FuncDeclKind.OR;
    } else if (symbol == t.mNot) {
      return FuncDeclKind.NOT;
    } else if (symbol == t.mImplies) {
      return FuncDeclKind.IMPLIES;
    } else if (symbol == t.mXor) {
      return FuncDeclKind.XOR;

      // Polymorphic function symbols are more difficult.
    } else if (symbol.getName().equals("=")) {
      return FuncDeclKind.EQ;
    } else if (symbol.getName().equals("distinct")) {
      return FuncDeclKind.DISTINCT;
    } else if (symbol.getName().equals("ite")) {
      return FuncDeclKind.ITE;
    } else if (isVariable(input)) {
      return FuncDeclKind.VAR;
    } else {

      // TODO: other declaration kinds!
      return FuncDeclKind.OTHER;
    }
  }
}
