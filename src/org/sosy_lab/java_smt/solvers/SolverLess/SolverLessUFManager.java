// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

public class SolverLessUFManager
    extends AbstractUFManager<SMTLIB2Formula, DummyFunction, DummyType, DummyEnv> {

  protected SolverLessUFManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }
}
