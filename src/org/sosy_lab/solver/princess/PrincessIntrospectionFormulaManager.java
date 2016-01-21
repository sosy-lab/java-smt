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

import static org.sosy_lab.solver.princess.PrincessUtil.isBoolean;
import static org.sosy_lab.solver.princess.PrincessUtil.isUIF;

import ap.basetypes.IdealInt;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFunApp;
import ap.parser.IIntLit;

import com.google.common.base.Function;

import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.FuncDeclKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.AbstractIntrospectionFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;

class PrincessIntrospectionFormulaManager
    extends AbstractIntrospectionFormulaManager<IExpression, TermType, PrincessEnvironment> {

  private final PrincessFormulaCreator formulaCreator;

  PrincessIntrospectionFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
    formulaCreator = pCreator;
  }

  private IExpression replaceArgs(IExpression pT, List<IExpression> newArgs) {
    return PrincessUtil.replaceArgs(pT, newArgs);
  }

  private TermType getType(IExpression t) {
    return isBoolean(t) ? TermType.Boolean : TermType.Integer;
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
    } else if (PrincessUtil.isBoundByQuantifier(input)) {
      return visitor.visitBoundVariable(f, PrincessUtil.getIndex(input));
    } else if (PrincessUtil.isVariable(input)) {
      return visitor.visitFreeVariable(f, input.toString());
    } else {
      int arity = PrincessUtil.getArity(input);
      String name;
      if (isUIF(input)) {
        name = ((IFunApp) input).fun().name();
      } else {
        name = toString();
      }
      List<Formula> args = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        IExpression arg = PrincessUtil.getArg(input, i);
        FormulaType<?> argumentType = formulaCreator.getFormulaType(arg);
        args.add(formulaCreator.encapsulate(argumentType, arg));
      }

      // Any function application.
      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return formulaCreator.encapsulateWithTypeOf(
                  PrincessUtil.replaceArgs(input, extractInfo(formulas)));
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
    } else if (PrincessUtil.isVariable(input)) {
      return FuncDeclKind.VAR;
    } else {

      // TODO: other cases!!!
      return FuncDeclKind.OTHER;
    }
  }
}
