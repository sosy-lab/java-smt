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
package org.sosy_lab.solver.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.solver.princess.PrincessUtil.isBoolean;

import ap.basetypes.IdealInt;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;

import com.google.common.base.Function;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.FuncDeclKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.AbstractUnsafeFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

class PrincessUnsafeFormulaManager
    extends AbstractUnsafeFormulaManager<IExpression, TermType, PrincessEnvironment> {

  private final PrincessFormulaCreator formulaCreator;

  PrincessUnsafeFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
    formulaCreator = pCreator;
  }

  @Override
  public int getArity(IExpression pT) {
    return PrincessUtil.getArity(pT);
  }

  @Override
  public IExpression getArg(IExpression pT, int pN) {
    return PrincessUtil.getArg(pT, pN);
  }

  @Override
  public boolean isVariable(IExpression pT) {
    return PrincessUtil.isVariable(pT);
  }

  @Override
  public boolean isUF(IExpression t) {
    return PrincessUtil.isUIF(t);
  }

  @Override
  public String getName(IExpression t) {
    if (isUF(t)) {
      return ((IFunApp) t).fun().name();
    } else {
      return t.toString();
    }
  }

  @Override
  public IExpression replaceArgs(IExpression pT, List<IExpression> newArgs) {
    return PrincessUtil.replaceArgs(pT, newArgs);
  }

  TermType getType(IExpression t) {
    return isBoolean(t) ? TermType.Boolean : TermType.Integer;
  }

  @Override
  public IExpression replaceArgsAndName(IExpression t, String pNewName, List<IExpression> newArgs) {

    if (isVariable(t)) {
      checkArgument(newArgs.isEmpty());

      // when no new name is given we need to use the old variable
      if (t.toString().equals(pNewName)) {
        return t;
      }

      return getFormulaCreator().makeVariable(getType(t), pNewName);

    } else if (isUF(t)) {
      IFunApp fun = (IFunApp) t;
      PrincessEnvironment env = getFormulaCreator().getEnv();
      TermType returnType = env.getReturnTypeForFunction(fun.fun());
      return env.makeFunction(env.declareFun(pNewName, fun.args().size(), returnType), newArgs);

    } else {
      throw new IllegalArgumentException("The Term " + t + " has no name!");
    }
  }

  @Override
  public Formula substitute(Formula pF, Map<Formula, Formula> pFromToMapping) {
    return substituteUsingMap(pF, pFromToMapping);
  }

  @Override
  protected List<? extends IExpression> splitNumeralEqualityIfPossible(IExpression pF) {
    // Princess does not support Equal.
    // Formulas are converted from "a==b" to "a+(-b)==0".
    if (pF instanceof IIntFormula && ((IIntFormula) pF).rel() == IIntRelation.EqZero()) {
      return ImmutableList.of(
          ((IIntFormula) pF).t().$less$eq(new IIntLit(IdealInt.ZERO())),
          ((IIntFormula) pF).t().$greater$eq(new IIntLit(IdealInt.ZERO())));
    }
    return ImmutableList.of(pF);
  }

  @Override
  public boolean isNumber(IExpression pT) {
    return PrincessUtil.isNumber(pT);
  }

  @Override
  protected boolean isFreeVariable(IExpression pT) {
    return isVariable(pT);
  }

  @Override
  protected boolean isBoundVariable(IExpression pT) {
    return PrincessUtil.isBoundByQuantifier(pT);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula f, final IExpression input) {
    if (input instanceof IIntLit) {
      IdealInt value = ((IIntLit) input).value();
      return visitor.visitConstant(f, value.bigIntValue());
    } else if (input instanceof IBoolLit) {
      IBoolLit literal = (IBoolLit) input;
      return visitor.visitConstant(f, literal.value());
    } else if (PrincessUtil.isQuantifier(input)) {
      BooleanFormula body =
          formulaCreator.encapsulateBoolean(PrincessUtil.getQuantifierBody(input));
      return visitor.visitQuantifier(
          (BooleanFormula) f,
          PrincessUtil.isForall(input) ? Quantifier.FORALL : Quantifier.EXISTS,

          // Princess does not hold any metadata about bound variables,
          // so we can't get meaningful list here.
          // HOWEVER, passing this list to QuantifiedFormulaManager#mkQuantifier
          // works as expected.
          new ArrayList<Formula>(),
          body);
    } else if (isBoundVariable(input)) {
      return visitor.visitBoundVariable(f, PrincessUtil.getIndex(input));
    } else if (isVariable(input)) {
      return visitor.visitFreeVariable(f, getName(input));
    } else {
      int arity = getArity(input);
      String name = getName(input);
      final FormulaType<?> type = formulaCreator.getFormulaType(input);
      List<Formula> args = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        IExpression arg = getArg(input, i);
        FormulaType<?> argumentType = formulaCreator.getFormulaType(arg);
        args.add(formulaCreator.encapsulate(argumentType, arg));
      }

      // Any function application.
      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return replaceArgs(formulaCreator.encapsulate(type, input), formulas);
            }
          };
      return visitor.visitFuncApp(
          f, args, FuncDecl.of(name, getDeclarationKind(input)), constructor);
    }
  }

  private FuncDeclKind getDeclarationKind(IExpression input) {
    if (PrincessUtil.isIfThenElse(input)) {
      return FuncDeclKind.ITE;
    } else if (PrincessUtil.isUIF(input)) {
      return FuncDeclKind.UF;
    } else if (PrincessUtil.isAnd(input)) {
      return FuncDeclKind.AND;
    } else if (PrincessUtil.isOr(input)) {
      return FuncDeclKind.OR;
    } else if (PrincessUtil.isNot(input)) {
      return FuncDeclKind.NOT;
    } else if (PrincessUtil.isEquivalence(input)) {
      return FuncDeclKind.IFF;
    } else if (PrincessUtil.isIfThenElse(input)) {
      return FuncDeclKind.ITE;
    } else if (isVariable(input)) {
      return FuncDeclKind.VAR;
    } else {

      // TODO: other cases!!!
      return FuncDeclKind.OTHER;
    }
  }
}
