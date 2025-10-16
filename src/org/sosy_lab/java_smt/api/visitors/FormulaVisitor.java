// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

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
   * <p>This method is deprecated because bound variables are no longer explicitly visited. When
   * entering a quantified formula, bound variables are seen as free variables, as documented in
   * {@link #visitQuantifier}. When entering the body of a quantified formula, bound variables are
   * replaced by free variables, and are visited with {@link #visitFreeVariable}.
   *
   * @param f Formula representing the variable.
   * @param deBruijnIdx de-Bruijn index of the bound variable, which can be used to find the
   *     matching quantifier.
   */
  default R visitBoundVariable(Formula f, int deBruijnIdx) {
    throw new UnsupportedOperationException(
        "Bound variables are no longer explicitly visited in JavaSMT. "
            + "Use a combination of 'visitQuantifier' (for the whole quantified formula) and "
            + "'visitFreeVariable' (in the body) instead.");
  }

  /**
   * Visit a constant, such as "true"/"false", a numeric constant like "1" or "1.0", a String
   * constant like 2hello world" or enumeration constant like "Blue".
   *
   * @param f Formula representing the constant.
   * @param value The value of the constant. It is either of type {@link Boolean}, of a subtype of
   *     {@link Number} (mostly a {@link BigInteger}, a {@link BigDecimal}, or a {@link Rational}),
   *     or {@link String}.
   * @return An arbitrary return value that is passed to the caller.
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
   * @param boundVariables Variables bound by the quantifier. The variables are provided as free
   *     variables, such that they can be used as normal symbols in JavaSMT. <b>NOTE:</b> not all
   *     solvers hold metadata about bound variables. In case this is not available, this method
   *     will be called with an empty list, yet {@code #mkQuantifier} will work fine with an empty
   *     list as well.
   * @param body Body of the quantifier. The body is provided without bound variables, i.e., all
   *     bound variables from this quantifier application are provided as free variables.
   */
  R visitQuantifier(
      BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body);
}
