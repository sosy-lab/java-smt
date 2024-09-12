// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.collect.ImmutableMap;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class CVC5TheoremProver extends CVC5AbstractProver<Void>
    implements ProverEnvironment, BasicProverEnvironment<Void> {

  protected CVC5TheoremProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      @SuppressWarnings("unused") int randomSeed,
      Set<ProverOptions> pOptions,
      FormulaManager pMgr,
      ImmutableMap<String, String> pFurtherOptionsMap) {
    super(pFormulaCreator, pShutdownNotifier, randomSeed, pOptions, pMgr, pFurtherOptionsMap);
  }

  @Override
  @Nullable
  protected Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    addConstraint0(constraint);
    return null;
  }
}
