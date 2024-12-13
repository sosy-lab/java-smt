// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public class InterpolatingSolverStackOptimizationTest extends InterpolatingSolverStackTest0 {

  @Override
  protected BasicProverEnvironment<?> newEnvironmentForTest(
      SolverContext pContext, ProverOptions... options) {
    requireOptimization();
    return pContext.newOptimizationProverEnvironment(options);
  }
}
