// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class SmtInterpolTheoremProver extends SmtInterpolAbstractProver<Void>
    implements ProverEnvironment {

  SmtInterpolTheoremProver(
      SmtInterpolFormulaManager pMgr,
      Script pEnv,
      Set<ProverOptions> options,
      ShutdownNotifier pShutdownNotifier) {
    super(pMgr, pEnv, options, pShutdownNotifier);
  }

  @Override
  protected Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    addConstraint0(constraint);
    return null;
  }
}
