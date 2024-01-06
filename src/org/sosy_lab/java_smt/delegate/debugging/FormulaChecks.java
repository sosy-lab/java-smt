// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.truth.Truth.assertWithMessage;

import org.sosy_lab.java_smt.api.Formula;
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
    nodeManager.addFormulaToContext(pFormula);
  }

  /** Assert that the formula belongs to this context. */
  public void assertFormulaInContext(Formula pFormula) {
    assertWithMessage("Solver object was not defined in this context.")
        .that(nodeManager.isInContext(pFormula))
        .isTrue();
  }
}
