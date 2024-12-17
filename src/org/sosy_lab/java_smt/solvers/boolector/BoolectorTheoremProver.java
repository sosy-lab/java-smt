// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class BoolectorTheoremProver extends BoolectorAbstractProver<Void> implements ProverEnvironment {
  // Used as standard prover. Built by method newProverEnvironment0 in BtorSolverContext

  protected BoolectorTheoremProver(
      BoolectorFormulaManager manager,
      BoolectorFormulaCreator creator,
      long btor,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      AtomicBoolean pIsAnyStackAlive) {
    super(manager, creator, btor, pShutdownNotifier, pOptions, pIsAnyStackAlive);
  }
}
