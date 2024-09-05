// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtSolverContext.OpenSMTOptions;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;

class OpenSmtTheoremProver extends OpenSmtAbstractProver<Formula> implements ProverEnvironment {

  OpenSmtTheoremProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      OpenSMTOptions pSolverOptions) {
    super(
        pFormulaCreator,
        pMgr,
        pShutdownNotifier,
        getConfigInstance(pOptions, pSolverOptions, false),
        pOptions);
  }

  @Override
  public Formula addConstraintImpl(PTRef f) throws InterruptedException {
    osmtSolver.insertFormula(f);
    return (Formula) f;
  }
}
