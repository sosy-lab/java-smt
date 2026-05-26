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
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;

/**
 * A formula visitor which allows for the default implementation.
 *
 * @param <R> Return type for each traversal operation.
 */
public abstract class DefaultBooleanFormulaVisitor<R> implements BooleanFormulaVisitor<R> {

  protected abstract R visitDefault();

  @Override
  public R visitConstant(boolean value) {
    return visitDefault();
  }

  @Override
  public R visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
    return visitDefault();
  }

  @Override
  public R visitNot(BooleanFormula pOperand) {
    return visitDefault();
  }

  @Override
  public R visitAnd(List<BooleanFormula> pOperands) {
    return visitDefault();
  }

  @Override
  public R visitOr(List<BooleanFormula> pOperands) {
    return visitDefault();
  }

  @Override
  public R visitXor(BooleanFormula operand1, BooleanFormula operand2) {
    return visitDefault();
  }

  @Override
  public R visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return visitDefault();
  }

  @Override
  public R visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return visitDefault();
  }

  @Override
  public R visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return visitDefault();
  }

  @Override
  public R visitQuantifier(
      Quantifier quantifier,
      BooleanFormula quantifiedAST,
      List<Formula> boundVars,
      BooleanFormula body) {
    return visitDefault();
  }
}
