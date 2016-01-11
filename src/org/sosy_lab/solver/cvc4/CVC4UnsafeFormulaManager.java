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

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractUnsafeFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class CVC4UnsafeFormulaManager
    extends AbstractUnsafeFormulaManager<Expr, Type, CVC4Environment> {

  private final CVC4FormulaCreator formulaCreator;

  CVC4UnsafeFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    formulaCreator = pCreator;
  }

  @Override
  protected boolean isAtom(Expr pT) {
    return pT.isConst() || pT.isVariable();
  }

  @Override
  protected int getArity(Expr pT) {
    return (int) pT.getNumChildren();
  }

  @Override
  protected Expr getArg(Expr pT, int pN) {
    return pT.getChild(pN);
  }

  @Override
  protected boolean isVariable(Expr pT) {
    return pT.isVariable();
  }

  @Override
  protected boolean isFreeVariable(Expr pT) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  protected boolean isBoundVariable(Expr pT) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  protected boolean isQuantification(Expr pT) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  protected Expr getQuantifiedBody(Expr pT) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  protected Expr replaceQuantifiedBody(Expr pF, Expr pBody) {
    throw new UnsupportedOperationException("Quantifiers not implemented for CVC4");
  }

  @Override
  protected boolean isNumber(Expr pT) {
    return isAtom(pT) && pT.getType().isInteger(); // TODO float, rationals?
  }

  @Override
  protected boolean isUF(Expr pT) {
    return pT.getType().isFunction();
  }

  @Override
  protected String getName(Expr pT) {
    return pT.toString();
  }

  @Override
  protected Expr replaceArgsAndName(Expr pT, String pNewName, List<Expr> pNewArgs) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  protected Expr replaceArgs(Expr pT, List<Expr> pNewArgs) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  protected List<? extends Expr> splitNumeralEqualityIfPossible(Expr pF) {
    throw new UnsupportedOperationException("Not implemented");
  }

  @Override
  public Formula substitute(Formula pF, Map<Formula, Formula> pFromToMapping) {
    return substituteUsingMap(pF, pFromToMapping);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Expr f) {

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
      int arity = getArity(f);

      List<Formula> args = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        Expr arg = getArg(f, i);
        args.add(formulaCreator.encapsulate(formulaCreator.getFormulaType(arg), arg));
      }

      // Any function application.
      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return replaceArgs(formulaCreator.encapsulate(formulaCreator.getFormulaType(f), f), formulas);
            }
          };
      return visitor.visitFunction(formula, args, name, constructor, isUF(f));
    }
  }
}
