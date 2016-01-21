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
package org.sosy_lab.solver.cvc4;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.FuncDeclKind;
import org.sosy_lab.solver.basicimpl.AbstractIntrospectionFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;

public class CVC4IntrospectionFormulaManager
    extends AbstractIntrospectionFormulaManager<Expr, Type, CVC4Environment> {

  private final CVC4FormulaCreator formulaCreator;

  CVC4IntrospectionFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    formulaCreator = pCreator;
  }

  private Expr getArg(Expr pT, int pN) {
    return pT.getChild(pN);
  }

  private boolean isVariable(Expr pT) {
    return pT.isVariable();
  }

  private String getName(Expr pT) {
    Preconditions.checkState(!pT.isNull());

    if (pT.isConst() || pT.isVariable()) {
      return pT.toString();
    } else {
      return pT.getOperator().toString();
    }
  }

  private Expr replaceArgs(Expr pT, List<Expr> pNewArgs) {

    // TODO!
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Expr f) {
    Preconditions.checkState(!f.isNull());

    Type type = f.getType();

    if (f.isConst()) {
      if (type.isBoolean()) {
        return visitor.visitConstant(formula, f.getConstBoolean());
      } else if (type.isInteger() || type.isFloatingPoint()) {
        return visitor.visitConstant(formula, f.getConstRational());
      } else if (type.isBitVector()) {
        // TODO is this correct?
        return visitor.visitConstant(formula, f.getConstBitVector().getValue());
      } else {
        throw new UnsupportedOperationException("Unhandled constant kind");
      }

    } else if (f.isVariable()) {
      return visitor.visitFreeVariable(formula, getName(f));

    } else {
      String name = getName(f);
      long arity = f.getNumChildren();

      List<Formula> args = new ArrayList<>((int) arity);
      for (int i = 0; i < arity; i++) {
        Expr arg = getArg(f, i);
        args.add(formulaCreator.encapsulate(formulaCreator.getFormulaType(arg), arg));
      }

      // Any function application.
      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return formulaCreator.encapsulateWithTypeOf(replaceArgs(f, extractInfo(formulas)));
            }
          };
      return visitor.visitFuncApp(
          formula, args, FuncDecl.of(name, getDeclarationKind(f)), constructor);
    }
  }

  private FuncDeclKind getDeclarationKind(Expr f) {
    Kind kind = f.getKind();
    if (kind == Kind.EQUAL) {
      return FuncDeclKind.EQ;
    } else if (kind == Kind.DISTINCT) {
      return FuncDeclKind.DISTINCT;
    } else if (kind == Kind.NOT) {
      return FuncDeclKind.NOT;
    } else if (kind == Kind.AND) {
      return FuncDeclKind.AND;
    } else if (kind == Kind.IFF) {
      return FuncDeclKind.IFF;
    } else if (kind == Kind.IMPLIES) {
      return FuncDeclKind.IMPLIES;
    } else if (kind == Kind.OR) {
      return FuncDeclKind.OR;
    } else if (kind == Kind.XOR) {
      return FuncDeclKind.XOR;
    } else if (kind == Kind.ITE) {
      return FuncDeclKind.ITE;
    } else if (kind == Kind.APPLY_UF) {
      return FuncDeclKind.UF;
    } else if (kind == Kind.PLUS) {
      return FuncDeclKind.ADD;
    } else if (kind == Kind.MULT) {
      return FuncDeclKind.MUL;
    } else if (kind == Kind.MINUS) {
      return FuncDeclKind.SUB;
    } else if (kind == Kind.DIVISION) {
      return FuncDeclKind.DIV;
    } else if (kind == Kind.LT) {
      return FuncDeclKind.LT;
    } else if (kind == Kind.LEQ) {
      return FuncDeclKind.LTE;
    } else if (kind == Kind.GT) {
      return FuncDeclKind.GT;
    } else if (kind == Kind.GEQ) {
      return FuncDeclKind.GTE;
    } else {
      return FuncDeclKind.OTHER;
    }
  }
}
