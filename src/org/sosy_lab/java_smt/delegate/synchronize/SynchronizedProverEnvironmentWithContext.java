// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

class SynchronizedProverEnvironmentWithContext
    extends SynchronizedBasicProverEnvironmentWithContext<Void> implements ProverEnvironment {

  SynchronizedProverEnvironmentWithContext(
      ProverEnvironment pDelegate,
      SolverContext pSync,
      FormulaManager pManager,
      FormulaManager pOtherManager) {
    super(pDelegate, pSync, pManager, pOtherManager);
  }
}
