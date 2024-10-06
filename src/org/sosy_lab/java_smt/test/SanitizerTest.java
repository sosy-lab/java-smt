/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static org.junit.Assert.assertThrows;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class SanitizerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Before
  public void init() {
    requireParser();
    requireIntegers();
  }

  @Test
  public void logicTest() throws SolverException, InterruptedException {
    // Valid input string that sets the logic to QF_ALL
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    String validLogic = "(set-logic QF_ALL)" + "(declare-const v Int)" + "(assert (= v 3))";
    assertThatFormula(mgr.parse(validLogic)).isEquivalentTo(expected);

    // Invalid string that sets logic QF_UF, even though integers are needed
    // FIXME: We don't check for this as most solvers seem to ignore the logic anyway
    String wrongLogic = "(set-logic QF_UF)" + "(declare-const v Int)" + "(assert (= v 3))";
    assertThatFormula(mgr.parse(wrongLogic)).isEquivalentTo(expected);

    // Try setting logic after another command was already used
    String logicAfterOption =
        "(set-option :produce-models true)"
            + "(set-logic ALL)"
            + "(declare-const v Int)"
            + "(assert (= v 3))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(logicAfterOption));

    // Try setting the logic again after it has already been set
    String logicTwice =
        "(set-logic ALL)" + "(declare-const v Int)" + "(set-logic QF_UF)" + " (assert (= v 3))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(logicTwice));

    // Call (reset) and *then* set the logic again
    // FIXME: We currently don't support the (reset) command and expect and exception to be thrown
    // here
    String logicReset =
        "(set-logic QF_UF)"
            + "(reset)"
            + "(set-logic ALL)"
            + "(declare-const v Int)"
            + "(assert (= v 3))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(logicReset));
  }

  @Test
  public void exitAtTheEnd() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)" + "(assert (= v 3))");

    // A valid input string with (exit) at the end
    BooleanFormula exitAtTheEnd =
        mgr.parse("(declare-const v Int)" + "(assert (= v 3))" + "(exit)");
    assertThatFormula(expected).isEquivalentTo(exitAtTheEnd);

    // An invalid input string where (exit) is used before the end of the file
    String exitNotAtTheEnd =
        "(declare-const v Int)" + "(assert (= v 3))" + "(exit)" + "(assert (= v 0))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(exitNotAtTheEnd));
  }

  @Test
  public void stackPushTest() throws SolverException, InterruptedException {
    // FIXME: We currently don't support stack operations and expect an exceptions to be thrown for
    // these inputs

    // Push an assertion and then use (pop) to remove it again
    String stackPush =
        "(declare-const v Int)" + "(push 1)" + "(assert (= v 0))" + "(pop 1)" + "(assert (= v 3))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(stackPush));

    // Use (reset-assertions) to remove all assertions from the stack
    String stackResetAssertions =
        "(declare-const v Int)"
            + "(assert (= v 3))"
            + "(reset-assertions)"
            + "(declare-const v Int)"
            + "(assert (= v 0))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(stackResetAssertions));

    // With :global-declarations the reset will also remove all declarations
    String globalStackResetAssertions =
        "(set-option :global-declarations true)"
            + "(declare-const v Int)"
            + "(assert (= v 3))"
            + "(reset-assertions)"
            + "(assert (= v 0))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(globalStackResetAssertions));

    // Just calling (reset) will also clear the stack
    String stackReset =
        "(declare-const v Int)"
            + "(assert (= v 0))"
            + "(reset)"
            + "(declare-const v Int)"
            + "(assert (= v 3))";
    assertThrows(IllegalArgumentException.class, () -> mgr.parse(stackReset));
  }
}
