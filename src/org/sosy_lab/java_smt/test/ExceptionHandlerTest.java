// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

/** Test that exception handling is set up properly. */
public class ExceptionHandlerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Before
  public void setup() {
    assume().that(solverToUse()).isNotEqualTo(Solvers.SOLVERLESS);
  }

  @Test(expected = Exception.class)
  @SuppressWarnings("CheckReturnValue")
  public void testErrorHandling() {
    // Will exit(1) without an exception handler.
    rmgr.makeNumber("not-a-number");
  }
}
