// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import org.junit.Test;
import org.sosy_lab.java_smt.api.SolverException;

/** Deterministic regression tests for LeanSMT satisfiability result handling. */
public class LeanSmtTheoremProverResultHandlingTest {

  @Test
  public void unknownResultThrowsSolverException() {
    SolverException ex =
        assertThrows(
            SolverException.class,
            () ->
                LeanSmtTheoremProver.throwOnUnknownOrUnexpectedResult(
                    true, 2, "satisfiability check"));
    assertThat(ex).hasMessageThat().contains("returned UNKNOWN");
  }

  @Test
  public void unexpectedResultCodeThrowsSolverException() {
    SolverException ex =
        assertThrows(
            SolverException.class,
            () ->
                LeanSmtTheoremProver.throwOnUnknownOrUnexpectedResult(
                    false, 42, "satisfiability check"));
    assertThat(ex).hasMessageThat().contains("Unexpected LeanSMT satisfiability result");
  }
}
