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
package org.sosy_lab.solver.visitors;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.List;

/**
 * Abstract class for formula transformation.
 *
 * @see org.sosy_lab.solver.api.FormulaManager#transformRecursively
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
  public Formula visitBoundVariable(Formula f, int deBruijnIdx) {
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
   *
   * @return Transformed function.
   */
  @Override
  public Formula visitFunction(
      Formula f, List<Formula> newArgs, FunctionDeclaration<?> functionDeclaration) {
    return fmgr.makeApplication(functionDeclaration, newArgs);
  }

  /**
   *
   * @param f Quantifier formula.
   * @param quantifier Quantifier type: either {@code FORALL} or {@code EXISTS}.
   * @param boundVariables Variables bound by the quantifier.
   *                       <b>NOTE:</b> not all solvers hold metadata about
   *                       bound variables.
   *                       In case this is not available, this method will be
   *                       called with an empty list, yet {@code mkQuantifier}
   *                       will work fine with an empty list as well.
   * @param transformedBody Quantifier body <b>already transformed</b> by the
   *                        visitor.
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
