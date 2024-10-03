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
  public void validLogicTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse("(set-logic QF_ALL)" + "(declare-const v Int)" + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test(expected = IllegalArgumentException.class)
  public void wrongLogicTest() throws SolverException, InterruptedException {
    // When we change the code to not use sanitize() solver seem to just ignore set-logic
    // Except for OpenSMT, which always crashes
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse("(set-logic QF_UF)" + "(declare-const v Int)" + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test(expected = IllegalArgumentException.class)
  public void logicAfterOptionTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(set-option :produce-models true)"
                + "(set-logic ALL)"
                + "(declare-const v Int)"
                + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test(expected = IllegalArgumentException.class)
  public void logicUsedTwiceTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(set-logic ALL)" + "(declare-const v Int)" + "(set-logic QF_UF)" + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test
  public void exitAtTheEnd() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken = mgr.parse("(declare-const v Int)" + "(assert (= v 3))" + "(exit)");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test(expected = IllegalArgumentException.class)
  public void exitNotTheEnd() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse("(declare-const v Int)" + "(assert (= v 3))" + "(exit)" + "(assert (= v 0))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test
  public void logicResetTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(set-logic QF_UF)"
                + "(reset)"
                + "(set-logic ALL)"
                + "(declare-const v Int)"
                + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test
  public void stackPushTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(declare-const v Int)"
                + "(push 1)"
                + "(assert (= v 0))"
                + "(pop 1)"
                + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test
  public void stackResetAssertionsTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(declare-const v Int)"
                + "(assert (= v 3))"
                + "(reset-assertions)"
                + "(declare-const v Int)"
                + "(assert (= v 0))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test
  public void globalStackResetAssertionsTest() throws SolverException, InterruptedException {
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(set-option :global-declarations true)"
                + "(declare-const v Int)"
                + "(assert (= v 3))"
                + "(reset-assertions)"
                + "(assert (= v 0))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }

  @Test
  public void stackResetTest() throws SolverException, InterruptedException {
    requireParser();
    requireIntegers();
    BooleanFormula expected = mgr.parse("(declare-const v Int)(assert (= v 3))");
    BooleanFormula broken =
        mgr.parse(
            "(declare-const v Int)"
                + "(assert (= v 0))"
                + "(reset)"
                + "(declare-const v Int)"
                + "(assert (= v 3))");
    assertThatFormula(expected).isEquivalentTo(broken);
  }
}
