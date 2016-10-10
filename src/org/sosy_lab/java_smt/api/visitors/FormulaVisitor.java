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
package org.sosy_lab.java_smt.api.visitors;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;

/**
 * Visitor iterating through entire formula. Use {@link FormulaManager#visit} for visiting formulas.
 *
 * @param <R> Desired return type.
 */
public interface FormulaVisitor<R> {

  /**
   * Visit a free variable (such as "x", "y" or "z"), not bound by a quantifier. The variable can
   * have any sort (both boolean and non-boolean).
   *
   * @param f Formula representing the variable.
   * @param name Variable name.
   */
  R visitFreeVariable(Formula f, String name);

  /**
   * Visit a variable bound by a quantifier. The variable can have any sort (both boolean and
   * non-boolean).
   *
   * @param f Formula representing the variable.
   * @param deBruijnIdx de-Bruijn index of the bound variable, which can be used to find the
   *     matching quantifier.
   */
  R visitBoundVariable(Formula f, int deBruijnIdx);

  /**
   * Visit a constant, such as "true"/"false" or a numeric constant like "1" or "1.0".
   *
   * @param f Formula representing the constant.
   * @param value The value of the constant. It is either of type {@link Boolean} or of a subtype of
   *     {@link Number}, mostly a {@link BigInteger}, a {@link BigDecimal}, or a {@link Rational}.
   * @return An arbitrary return value that is be passed to the caller.
   */
  R visitConstant(Formula f, Object value);

  /**
   * Visit an arbitrary, potentially uninterpreted function. The function can have any sort.
   *
   * @param f Input function.
   * @param args List of arguments
   * @param functionDeclaration Function declaration. Can be given to {@link
   *     FormulaManager#makeApplication} to construct a new instance of the same function with
   *     different arguments.
   */
  R visitFunction(Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration);

  /**
   * Visit a quantified node.
   *
   * @param f Quantifier formula.
   * @param quantifier Quantifier type: either {@code FORALL} or {@code EXISTS}.
   * @param boundVariables Variables bound by the quantifier. <b>NOTE:</b> not all solvers hold
   *     metadata about bound variables. In case this is not available, this method will be called
   *     with an empty list, yet {@code mkQuantifier} will work fine with an empty list as well.
   * @param body Body of the quantifier.
   */
  R visitQuantifier(
      BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body);
}
