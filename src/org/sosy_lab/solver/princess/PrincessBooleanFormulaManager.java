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
package org.sosy_lab.solver.princess;

import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.INot;
import ap.parser.ITerm;
import ap.parser.ITermITE;

import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;

import scala.Enumeration;

class PrincessBooleanFormulaManager
    extends AbstractBooleanFormulaManager<
        IExpression, PrincessTermType, PrincessEnvironment, PrincessFunctionDeclaration> {

  PrincessBooleanFormulaManager(PrincessFormulaCreator creator) {
    super(creator);
  }

  @Override
  public IFormula makeVariableImpl(String varName) {
    return (IFormula) getFormulaCreator().makeVariable(getFormulaCreator().getBoolType(), varName);
  }

  @Override
  public IFormula makeBooleanImpl(boolean pValue) {
    return new IBoolLit(pValue);
  }

  @Override
  public IFormula equivalence(IExpression t1, IExpression t2) {
    return new IBinFormula(IBinJunctor.Eqv(), (IFormula) t1, (IFormula) t2);
  }

  @Override
  public boolean isTrue(IExpression t) {
    return t instanceof IBoolLit && ((IBoolLit) t).value();
  }

  @Override
  public boolean isFalse(IExpression t) {
    return t instanceof IBoolLit && !((IBoolLit) t).value();
  }

  @Override
  public IExpression ifThenElse(IExpression condition, IExpression t1, IExpression t2) {
    if (t1 instanceof IFormula) {
      return new IFormulaITE((IFormula) condition, (IFormula) t1, (IFormula) t2);
    } else {
      return new ITermITE((IFormula) condition, (ITerm) t1, (ITerm) t2);
    }
  }

  @Override
  public IFormula not(IExpression pBits) {
    if (pBits instanceof INot) {
      return ((INot) pBits).subformula(); // "not not a" == "a"
    } else {
      return new INot((IFormula) pBits);
    }
  }

  @Override
  public IFormula and(IExpression t1, IExpression t2) {
    if (t1.equals(t2)) {
      return (IFormula) t1;
    }
    if (isTrue(t1)) {
      return (IFormula) t2;
    }
    if (isTrue(t2)) {
      return (IFormula) t1;
    }
    return simplify(new IBinFormula(IBinJunctor.And(), (IFormula) t1, (IFormula) t2));
  }

  @Override
  public IFormula or(IExpression t1, IExpression t2) {
    if (isFalse(t1)) {
      return (IFormula) t2;
    }
    if (isFalse(t2)) {
      return (IFormula) t1;
    }
    return simplify(new IBinFormula(IBinJunctor.Or(), (IFormula) t1, (IFormula) t2));
  }

  /** simplification to avoid identical subgraphs: (a&b)&(a&c) --> a&(b&c), etc */
  private IFormula simplify(IFormula f) {
    if (f instanceof IBinFormula) {
      final IBinFormula bin = (IBinFormula) f;
      if (bin.f1() instanceof IBinFormula
          && bin.f2() instanceof IBinFormula
          && ((IBinFormula) bin.f1()).j().equals(((IBinFormula) bin.f2()).j())) {
        Enumeration.Value operator = ((IBinFormula) f).j();
        Enumeration.Value innerOperator = ((IBinFormula) bin.f1()).j();

        IFormula s11 = ((IBinFormula) bin.f1()).f1();
        IFormula s12 = ((IBinFormula) bin.f1()).f2();
        IFormula s21 = ((IBinFormula) bin.f2()).f1();
        IFormula s22 = ((IBinFormula) bin.f2()).f2();

        if (s11.equals(s21)) { // (ab)(ac) -> a(bc)
          return new IBinFormula(innerOperator, s11, new IBinFormula(operator, s12, s22));
        } else if (s11.equals(s22)) { // (ab)(ca) -> a(bc)
          return new IBinFormula(innerOperator, s11, new IBinFormula(operator, s12, s21));
        } else if (s12.equals(s21)) { // (ba)(ac) -> a(bc)
          return new IBinFormula(innerOperator, s12, new IBinFormula(operator, s11, s22));
        } else if (s12.equals(s22)) { // (ba)(ca) -> a(bc)
          return new IBinFormula(innerOperator, s12, new IBinFormula(operator, s11, s21));
        }
      }
    }

    // if we cannot simplify the formula, we create an abbreviation
    // return getFormulaCreator().getEnv().abbrev(f);
    return f;
  }

  /**
   * {@inheritDoc}
   *
   * <p>Princess does not support XOR
   * Formulas are converted from {@code a^b} to {@code !(a<=>b)}
   */
  @Override
  public IFormula xor(IExpression t1, IExpression t2) {
    return new INot(new IBinFormula(IBinJunctor.Eqv(), (IFormula) t1, (IFormula) t2));
  }
}
