// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.util.Set;
import org.sosy_lab.java_smt.api.Formula;

/* Base class for all FormulaManagers and all other classes that need to handle formulas as
 * arguments. Adds a method to register formulas to the current context, and another that checks
 * if a given formula was created on this context.
 */
public class FormulaChecks extends ThreadChecks {
  protected final Set<Formula> localFormulas;

  public FormulaChecks(Set<Formula> pformulasInContext) {
    localFormulas = pformulasInContext;
  }

  /** Needs to be called after a new Formula is created to associate it with this context. */
  public void addFormulaToContext(Formula pFormula) {
    localFormulas.add(pFormula);
  }

  /** Assert that the formula belongs to this context. */
  public void assertFormulaInContext(Formula pFormula) {
    // TODO: Improve error reporting
    assert localFormulas.contains(pFormula);
  }
}
