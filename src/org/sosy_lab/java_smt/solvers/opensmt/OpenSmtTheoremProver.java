// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class OpenSmtTheoremProver extends OpenSmtAbstractProver<Void> implements ProverEnvironment {

  OpenSmtTheoremProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      int pRandom,
      Set<ProverOptions> pOptions) {

    super(pFormulaCreator, pMgr, pShutdownNotifier, getConfigInstance(pRandom, false), pOptions);
  }

  @Override
  @Nullable
  protected Void getConstraintName(BooleanFormula pF) {
    return null;
  }
}
