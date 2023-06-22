// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.INot;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.types.Sort;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import scala.Enumeration;

class PrincessBooleanFormulaManager
    extends AbstractBooleanFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  private final IBoolLit pTrue = new IBoolLit(true);
  private final IBoolLit pFalse = new IBoolLit(false);

  PrincessBooleanFormulaManager(PrincessFormulaCreator creator) {
    super(creator);
  }

  @Override
  public IFormula makeVariableImpl(String varName) {
    return (IFormula) getFormulaCreator().makeVariable(getFormulaCreator().getBoolType(), varName);
  }

  @Override
  public IFormula makeBooleanImpl(boolean pValue) {
    return pValue ? pTrue : pFalse;
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
    if (isTrue(condition)) {
      return t1;
    } else if (isFalse(condition)) {
      return t2;
    } else if (t1.equals(t2)) {
      return t1;
    } else if (isTrue(t1) && isFalse(t2)) {
      return condition;
    } else if (isFalse(t1) && isTrue(t2)) {
      return not(condition);
    }
    if (t1 instanceof IFormula) {
      return new IFormulaITE((IFormula) condition, (IFormula) t1, (IFormula) t2);
    } else {
      return new ITermITE((IFormula) condition, (ITerm) t1, (ITerm) t2);
    }
  }

  @Override
  public IFormula not(IExpression pBits) {
    if (isTrue(pBits)) {
      return pFalse;
    } else if (isFalse(pBits)) {
      return pTrue;
    } else if (pBits instanceof INot) {
      return ((INot) pBits).subformula(); // "not not a" == "a"
    } else {
      return new INot((IFormula) pBits);
    }
  }

  @Override
  public IFormula and(IExpression t1, IExpression t2) {
    if (t1 == t2) {
      return (IFormula) t1;
    } else if (isTrue(t1)) {
      return (IFormula) t2;
    } else if (isTrue(t2)) {
      return (IFormula) t1;
    } else if (isFalse(t1)) {
      return pFalse;
    } else if (isFalse(t2)) {
      return pFalse;
    }
    return simplify(new IBinFormula(IBinJunctor.And(), (IFormula) t1, (IFormula) t2));
  }

  @Override
  public IFormula or(IExpression t1, IExpression t2) {
    if (t1 == t2) {
      return (IFormula) t1;
    } else if (isTrue(t1)) {
      return pTrue;
    } else if (isTrue(t2)) {
      return pTrue;
    } else if (isFalse(t1)) {
      return (IFormula) t2;
    } else if (isFalse(t2)) {
      return (IFormula) t1;
    }
    return simplify(new IBinFormula(IBinJunctor.Or(), (IFormula) t1, (IFormula) t2));
  }

  /**
   * simplification based on distribution property of boolean operands, to avoid identical subgraphs
   * in basic boolean operations:
   *
   * <ul>
   *   <li>(a&b)&(a&c) --> a&(b&c)
   *   <li>(a|b)&(a|c) --> a|(b&c)
   *   <li>(a&b)|(a&c) --> a&(b|c)
   *   <li>(a|b)|(a|c) --> a|(b|c)
   * </ul>
   *
   * <p>Note that we only consider the most frequently used operations here. There are more
   * combination of boolean operators (implication and equivalence), which are ignored here, to keep
   * it simple.
   */
  private IFormula simplify(IFormula f) {
    if (f instanceof IBinFormula) {
      final IBinFormula bin = (IBinFormula) f;
      Enumeration.Value operator = bin.j();
      if (isDistributiveBooleanOperator(operator)
          && bin.f1() instanceof IBinFormula
          && bin.f2() instanceof IBinFormula
          && ((IBinFormula) bin.f1()).j().equals(((IBinFormula) bin.f2()).j())) {
        Enumeration.Value innerOperator = ((IBinFormula) bin.f1()).j();
        if (isDistributiveBooleanOperator(innerOperator)) {

          IFormula s11 = ((IBinFormula) bin.f1()).f1();
          IFormula s12 = ((IBinFormula) bin.f1()).f2();
          IFormula s21 = ((IBinFormula) bin.f2()).f1();
          IFormula s22 = ((IBinFormula) bin.f2()).f2();

          // only check for object equality, for performance
          if (s11 == s21) { // (ab)(ac) -> a(bc)
            return new IBinFormula(innerOperator, s11, new IBinFormula(operator, s12, s22));
          } else if (s11 == s22) { // (ab)(ca) -> a(bc)
            return new IBinFormula(innerOperator, s11, new IBinFormula(operator, s12, s21));
          } else if (s12 == s21) { // (ba)(ac) -> a(bc)
            return new IBinFormula(innerOperator, s12, new IBinFormula(operator, s11, s22));
          } else if (s12 == s22) { // (ba)(ca) -> a(bc)
            return new IBinFormula(innerOperator, s12, new IBinFormula(operator, s11, s21));
          }
        }
      }
    }

    // if we cannot simplify the formula, we create an abbreviation
    // return getFormulaCreator().getEnv().abbrev(f);
    return f;
  }

  private boolean isDistributiveBooleanOperator(Enumeration.Value operator) {
    return IBinJunctor.And().equals(operator) || IBinJunctor.Or().equals(operator);
  }

  /**
   * {@inheritDoc}
   *
   * <p>Princess does not support XOR Formulas are converted from {@code a^b} to {@code !(a<=>b)}
   */
  @Override
  public IFormula xor(IExpression t1, IExpression t2) {
    return new INot(new IBinFormula(IBinJunctor.Eqv(), (IFormula) t1, (IFormula) t2));
  }
}
