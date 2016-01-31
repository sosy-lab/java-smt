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

import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.IFunApp;
import ap.parser.IIntLit;
import ap.parser.INot;
import ap.parser.IQuantified;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.IVariable;

import com.google.common.base.Preconditions;

import scala.Enumeration;
import scala.collection.JavaConversions;

import java.util.List;

/** Static helper functions for Princess. */
class PrincessUtil {
  private PrincessUtil() {}

  /** ITerm is the arithmetic subclass of IExpression. */
  public static ITerm castToTerm(IExpression e) {
    return (ITerm) e;
  }

  /** IFormula is the boolean subclass of IExpression. */
  public static IFormula castToFormula(IExpression e) {
    return (IFormula) e;
  }

  public static boolean isVariable(IExpression t) {
    return t instanceof IAtom || t instanceof IConstant;
  }

  public static boolean isUF(IExpression t) {
    return (t instanceof IFunApp)
        && !((IFunApp) t).fun().name().equals("select")
        && !((IFunApp) t).fun().name().equals("store");
  }

  /** check for ConstantTerm with Number or
   * ApplicationTerm with negative Number */
  public static boolean isNumber(IExpression t) {
    return t instanceof IIntLit;
  }

  public static boolean isQuantifier(IExpression t) {
    return t instanceof IQuantified;
  }

  public static boolean isBoundByQuantifier(IExpression t) {
    return t instanceof IVariable;
  }

  public static boolean isForall(IExpression t) {
    return isQuantifier(t)
        && ((IQuantified) t).quan().equals(ap.terfor.conjunctions.Quantifier.apply(true));
  }

  /**
   * Returns de-Bruijn index for a quantified variable.
   */
  public static int getIndex(IExpression t) {
    Preconditions.checkState(isBoundByQuantifier(t));
    IVariable v = (IVariable) t;
    return v.index();
  }

  public static IExpression getQuantifierBody(IExpression t) {
    Preconditions.checkState(isQuantifier(t));
    return ((IQuantified) t).subformula();
  }

  public static boolean isBoolean(IExpression t) {
    // TODO: this is not always correct for UFs.
    return t instanceof IFormula;
  }

  public static boolean hasIntegerType(IExpression t) {
    return t instanceof ITerm;
  }

  /** t1 and t2 */
  public static boolean isAnd(IExpression t) {
    return isBinaryFunction(t, IBinJunctor.And());
  }

  /** t1 or t2 */
  public static boolean isOr(IExpression t) {
    return isBinaryFunction(t, IBinJunctor.Or());
  }

  /** not t */
  public static boolean isNot(IExpression t) {
    return t instanceof INot;
  }

  /** t1 => t2 */
  public static boolean isImplication(@SuppressWarnings("unused") IExpression t) {
    // Princess does not support implication.
    // Formulas are converted from "a=>b" to "!a||b".
    return false;
  }

  /** t1 or t2 */
  public static boolean isXor(@SuppressWarnings("unused") IExpression t) {
    // Princess does not support Xor.
    // Formulas are converted from "a^b" to "!(a<=>b)".
    return false;
  }

  /** (ite t1 t2 t3) */
  public static boolean isIfThenElse(IExpression t) {
    return t instanceof IFormulaITE // boolean args
        || t instanceof ITermITE; // arithmetic args
  }

  /** t1 = t2 */
  public static boolean isEquivalence(IExpression t) {
    return isBinaryFunction(t, IBinJunctor.Eqv());
  }

  private static boolean isBinaryFunction(IExpression t, Enumeration.Value val) {
    return (t instanceof IBinFormula)
        && val == ((IBinFormula) t).j(); // j is the operator and Scala is evil!
  }

  public static boolean isTrue(IExpression t) {
    return t instanceof IBoolLit && ((IBoolLit) t).value();
  }

  public static boolean isFalse(IExpression t) {
    return t instanceof IBoolLit && !((IBoolLit) t).value();
  }

  /** @return a new Term with the same function and new parameters. */
  public static IExpression replaceArgs(IExpression t, List<IExpression> newParams) {
    return t.update(JavaConversions.asScalaBuffer(newParams));
  }
}
