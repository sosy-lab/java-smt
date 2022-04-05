// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.api.Solver;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

/*
 * TODO: import/export of expressions is currently not supported, hence we need to use 1 solver
 * (context) for everything! They are working on it. See CVC5 github discussion.
 */
class CVC5TheoremProver extends CVC5AbstractProver<Void>
    implements ProverEnvironment, BasicProverEnvironment<Void> {

  protected CVC5TheoremProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      @SuppressWarnings("unused") int randomSeed,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      Solver pSolver) {
    super(pFormulaCreator, pShutdownNotifier, randomSeed, pOptions, pBmgr, pSolver);
  }
}
