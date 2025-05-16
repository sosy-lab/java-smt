/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public class PortfolioTheoremProver extends PortfolioAbstractProver<Void, ProverEnvironment>
    implements ProverEnvironment {

  protected PortfolioTheoremProver(
      Set<ProverOptions> pOptions,
      Map<Solvers, SolverContext> pSolverContexts,
      PortfolioFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    super(pOptions, pSolverContexts, pCreator, pShutdownNotifier, pLogger);
  }

  @Override
  ProverEnvironment getProver(
      SolverContext newEmptyContextWSameOptions, Set<ProverOptions> pOptions) {
    return newEmptyContextWSameOptions.newProverEnvironment(pOptions.toArray(new ProverOptions[0]));
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    for (ProverEnvironment prover : super.getCentralSolversAndProvers().values()) {
      prover.addConstraint(constraint);
    }
    return null;
  }
}
