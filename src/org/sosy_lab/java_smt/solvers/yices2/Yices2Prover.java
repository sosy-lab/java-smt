/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.yices2;

import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.solvers.yices2.Yices2SolverContext.Yices2Parameters;

class Yices2Prover extends Yices2AbstractProver<Void> implements ProverEnvironment {
  Yices2Prover(
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      Yices2Parameters pSolverParameters) {
    super(creator, pOptions, pBmgr, pShutdownNotifier, pSolverParameters);
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    addConstraint0(constraint);
    return null;
  }
}
