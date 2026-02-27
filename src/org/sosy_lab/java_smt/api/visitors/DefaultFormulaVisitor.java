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

public abstract class DefaultFormulaVisitor<R> implements FormulaVisitor<R> {

  /**
   * Method for default case, is called by all methods from this class if they are not overridden.
   *
   * @param f Formula for the currently visited node.
   * @return An arbitrary value, will be passed through to the caller.
   */
  protected abstract R visitDefault(Formula f);

  @Override
  public R visitFreeVariable(Formula f, String name) {
    return visitDefault(f);
  }

  @Override
  public R visitConstant(Formula f, Object value) {
    return visitDefault(f);
  }

  @Override
  public R visitFunction(
      Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
    return visitDefault(f);
  }

  @Override
  public R visitQuantifier(
      BooleanFormula f, Quantifier q, List<Formula> boundVariables, BooleanFormula body) {
    return visitDefault(f);
  }
}
