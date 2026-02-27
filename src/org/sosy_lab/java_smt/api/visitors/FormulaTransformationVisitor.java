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
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;

/**
 * Abstract class for formula transformation.
 *
 * @see org.sosy_lab.java_smt.api.FormulaManager#transformRecursively
 */
public abstract class FormulaTransformationVisitor implements FormulaVisitor<Formula> {

  private final FormulaManager fmgr;

  protected FormulaTransformationVisitor(FormulaManager fmgr) {
    this.fmgr = fmgr;
  }

  @Override
  public Formula visitFreeVariable(Formula f, String name) {
    return f;
  }

  @Override
  public Formula visitConstant(Formula f, Object value) {
    return f;
  }

  /**
   * @param f Input function.
   * @param newArgs New arguments <b>after</b> the transformation
   * @param functionDeclaration Function declaration
   * @return Transformed function.
   */
  @Override
  public Formula visitFunction(
      Formula f, List<Formula> newArgs, FunctionDeclaration<?> functionDeclaration) {
    return fmgr.makeApplication(functionDeclaration, newArgs);
  }

  /**
   * @param f Quantifier formula.
   * @param quantifier Quantifier type: either {@code FORALL} or {@code EXISTS}.
   * @param boundVariables Variables bound by the quantifier. <b>NOTE:</b> not all solvers hold
   *     metadata about bound variables. In case this is not available, this method will be called
   *     with an empty list, yet {@code #mkQuantifier} will work fine with an empty list as well.
   * @param transformedBody Quantifier body <b>already transformed</b> by the visitor.
   * @return Transformed AST
   */
  @Override
  public BooleanFormula visitQuantifier(
      BooleanFormula f,
      Quantifier quantifier,
      List<Formula> boundVariables,
      BooleanFormula transformedBody) {
    return fmgr.getQuantifiedFormulaManager()
        .mkQuantifier(quantifier, boundVariables, transformedBody);
  }
}
