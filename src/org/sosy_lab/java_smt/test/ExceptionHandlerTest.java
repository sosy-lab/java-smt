// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.junit.Assert.assertThrows;

import org.junit.Test;

/** Test that exception handling is set up properly. */
public class ExceptionHandlerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void testErrorHandling() {
    // Will exit(1) without an exception handler.
    assertThrows(Exception.class, () -> rmgr.makeNumber("not-a-number"));
  }
}
