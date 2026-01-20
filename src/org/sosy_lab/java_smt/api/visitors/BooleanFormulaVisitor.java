// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api.visitors;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;

/**
 * Visitor iterating through the boolean part of the formula. Use {@link
 * BooleanFormulaManager#visit} for visiting formulas.
 *
 * @param <R> Desired return type.
 */
public interface  BooleanFormulaVisitor<R> {

  /**
   * Visit a constant with a given value.
   *
   * @see BooleanFormulaManager#makeBoolean
   */
  R visitConstant(boolean value);

  /**
   * Visit a boolean variable bound by a quantifier.
   *
   * <p>Since JavaSMT no longer explicitly visits bound variables, and never has done so for most
   * solvers, this method will be removed in the future. Bound variables are available when visiting
   * a quantified formula, and can be accessed in {@link #visitQuantifier}. When entering the body
   * of a quantified formula, bound variables are seen as free variables, as documented in {@link
   * FormulaVisitor#visitQuantifier}.
   */
  @Deprecated(since = "2025.07, because bound variables are never created or used in the visitor")
  @SuppressWarnings("unused")
  default R visitBoundVar(BooleanFormula var, int deBruijnIdx) {
    throw new UnsupportedOperationException(
        "Bound variables are no longer explicitly visited in JavaSMT. "
            + "Use a combination of 'visitQuantifier' (for the whole quantified formula) and "
            + "'visitAtom' (for variables in the body) instead.");
  }

  /**
   * Visit a NOT-expression.
   *
   * @param operand Negated term.
   * @see BooleanFormulaManager#not
   */
  R visitNot(BooleanFormula operand);

  /**
   * Visit an AND-expression with an arbitrary number of boolean arguments.
   *
   * <p>An AND-expression with zero arguments is equisatisfiable to 'TRUE'. An AND-expression with
   * one argument is equal to the argument itself. In all other cases, default boolean logic
   * applies.
   *
   * @see BooleanFormulaManager#and
   */
  R visitAnd(List<BooleanFormula> operands);

  /**
   * Visit an OR-expression with an arbitrary number of boolean arguments.
   *
   * <p>An OR-expression with zero arguments is equisatisfiable to 'TRUE'. An OR-expression with one
   * argument is equal to the argument itself. In all other cases, default boolean logic applies.
   *
   * @see BooleanFormulaManager#or
   */
  R visitOr(List<BooleanFormula> operands);

  /**
   * Visit an XOR-expression.
   *
   * @see BooleanFormulaManager#xor
   */
  R visitXor(BooleanFormula operand1, BooleanFormula operand2);

  /**
   * Visit an equivalence between two formulas of boolean sort: {@code operand1 = operand2}.
   *
   * @see BooleanFormulaManager#equivalence
   */
  R visitEquivalence(BooleanFormula operand1, BooleanFormula operand2);

  /**
   * Visit an implication.
   *
   * @see BooleanFormulaManager#implication
   */
  R visitImplication(BooleanFormula operand1, BooleanFormula operand2);

  /**
   * Visit an if-then-else expression.
   *
   * @see BooleanFormulaManager#ifThenElse
   */
  R visitIfThenElse(
      BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula);

  /**
   * Visit a quantifier: forall- or exists-.
   *
   * @param quantifier Quantifier type: FORALL- or EXISTS-
   * @param quantifiedAST AST of the quantified node. Provided because it is difficult to re-create
   *     from the parameters.
   * @param boundVars Variables bound by this quantifier.
   * @param body Body of the quantified expression.
   * @see QuantifiedFormulaManager#mkQuantifier
   * @see QuantifiedFormulaManager#forall
   * @see QuantifiedFormulaManager#exists
   */
  R visitQuantifier(
      Quantifier quantifier,
      BooleanFormula quantifiedAST,
      List<Formula> boundVars,
      BooleanFormula body);

  /**
   * Visit an SMT atom. An atom can be a theory expression, constant, or a variable.
   *
   * <p>This is anything with a boolean sort which is not covered by the cases above.
   */
  R visitAtom(BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl);
}
