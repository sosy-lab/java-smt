// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;

import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

public class SolverStackInterpolationTest extends SolverStackTest0 {
  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  @Override
  protected void requireTheoryCombination() {
    assume()
        .withMessage(
            "Solver %s does not support the theory combination of INT and UFs for interpolation",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);
  }

  @Override
  protected BasicProverEnvironment<?> newEnvironmentForTest(
      SolverContext pContext, ProverOptions... options) {
    requireInterpolation();
    return pContext.newProverEnvironmentWithInterpolation(options);
  }
}
