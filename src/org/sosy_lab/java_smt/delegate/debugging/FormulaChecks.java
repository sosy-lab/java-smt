// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import com.google.common.base.Preconditions;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.delegate.debugging.DebuggingSolverContext.NodeManager;

/* Base class for all FormulaManagers and all other classes that need to handle formulas as
 * arguments. Adds a method to register formulas to the current context, and another that checks
 * if a given formula was created on this context.
 */
public class FormulaChecks extends ThreadChecks {
  protected final NodeManager nodeManager;

  public FormulaChecks(NodeManager pNodeManager) {
    nodeManager = pNodeManager;
  }

  /** Needs to be called after a new Formula is created to associate it with this context. */
  public void addFormulaToContext(Formula pFormula) {
    nodeManager.addFormulaTerm(pFormula);
  }

  /** Assert that the formula belongs to this context. */
  public void assertFormulaInContext(Formula pFormula) {
    Preconditions.checkArgument(
        nodeManager.isInFormulaTerms(pFormula),
        "Formula was not created in this context.\n  %s\nnot in\n  %s",
        pFormula,
        nodeManager.listFormulaTerms());
  }

  /** Needs to be called whenever a new UF is defined to associate it with this context. */
  public void addDeclarationToContext(FunctionDeclaration<?> pFunctionDeclaration) {
    nodeManager.addFunctionDeclaration(pFunctionDeclaration);
  }

  /** Assert that the function declaration belongs to this context. */
  public void assertDeclarationInContext(FunctionDeclaration<?> pFunctionDeclaration) {
    Preconditions.checkArgument(
        nodeManager.isInFunctionDeclarations(pFunctionDeclaration),
        "Function was not declared in this context.\n  %s\nnot in\n  %s",
        pFunctionDeclaration,
        nodeManager.listFunctionDeclarations());
  }
}
