// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class SolverContextTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void testMultipleContextClose() {
    context.close();
    context.close();
    context.close();
    context.close();
  }

  @Test
  public void testFormulaAccessAfterClose() {
    BooleanFormula term = bmgr.makeVariable("variable");
    BooleanFormula term2 = bmgr.makeVariable("variable");
    BooleanFormula term3 = bmgr.makeVariable("test");
    BooleanFormula termTrue = bmgr.makeBoolean(true);
    BooleanFormula termFalse = bmgr.makeBoolean(false);
    int hash = term.hashCode();
    context.close();

    // After calling 'close()', it depends on the solver whether we can further access any formula.
    // It would be nice to check for SegFault in a Junit test, but I do not know how to do that.

    // For the remaining test, we try to execute as much as possible after closing the context.

    // CVC5 does not allow any access after close()
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    assertThat(term).isEqualTo(term2);
    assertThat(term).isNotEqualTo(term3);
    assertThat(term).isNotEqualTo(termTrue);
    assertThat(termFalse).isNotEqualTo(termTrue);

    // Boolector allows nothing, lets abort here.
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    assertThat(term.hashCode()).isEqualTo(hash);

    // MathSAT5 allow nothing, lets abort here.
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.MATHSAT5);

    // Yices2 allows nothing, lets abort here.
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.YICES2);

    // Z3 seems to allows simple operations, but not deterministically, so better lets abort here.
    // Simple checks could even be ok (comparison against constants like TRUE/FALSE).
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    assertThat(bmgr.isTrue(term)).isFalse();
    assertThat(bmgr.isFalse(term)).isFalse();
    assertThat(bmgr.isTrue(termTrue)).isTrue();
    assertThat(bmgr.isFalse(termFalse)).isTrue();

    // try to access some data about formulae and managers
    assertThat(term.toString()).isEqualTo("variable");
    assertThat(term.hashCode()).isEqualTo(hash);
    assertThat(term).isEqualTo(term2);

    // For CVC4, we close the solver, however do not finalize and cleanup the terms,
    // thus direct access is possible, operations are forbidden.
    // See https://github.com/sosy-lab/java-smt/issues/169
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC4);

    // Java-based solvers allow more, i.e. they wait for GC, which is nice.

    // try to access some managers
    BooleanFormula notTerm = bmgr.not(term);
    assertThat(bmgr.isTrue(notTerm)).isFalse();
    assertThat(bmgr.isFalse(notTerm)).isFalse();

    BooleanFormula opTerm = bmgr.and(notTerm, term2);
    assertThat(bmgr.isTrue(opTerm)).isFalse();
    assertThat(bmgr.isFalse(opTerm)).isFalse();
  }

  @Test
  public void testProverCopying() throws SolverException, InterruptedException {
    requireProverCopying();
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      assertThat(prover.isUnsat()).isFalse();
      try (ProverEnvironment copiedProver = context.copyProverEnvironment(prover)) {
        assertThat(copiedProver.isUnsat()).isFalse();
      }
    }
  }

  @Test
  public void testProverCopyCloseInitialProver() throws SolverException, InterruptedException {
    requireProverCopying();
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      try (ProverEnvironment copiedProver = context.copyProverEnvironment(prover)) {
        prover.close();
        assertThat(copiedProver.isUnsat()).isFalse();
      }
    }
  }

  /*
   * Create a prover, push a SAT and an UNSAT formula on 2 levels, copy the prover, check that
   * the stack is copied correctly.
   */
  @Test
  public void testProverCopyWithStackAndAssertions() throws InterruptedException, SolverException {
    requireProverCopying();
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula one = imgr.makeNumber("1");
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      BooleanFormula sat = bmgr.and(imgr.equal(x, one), imgr.greaterOrEquals(x, one));
      BooleanFormula f = bmgr.makeFalse();
      prover.push();
      prover.addConstraint(sat);
      assertThat(prover.isUnsat()).isFalse();
      prover.push();
      prover.addConstraint(f);
      assertThat(prover.isUnsat()).isTrue();

      try (ProverEnvironment copiedProver = context.copyProverEnvironment(prover)) {
        assertThat(copiedProver.isUnsat()).isTrue();
        copiedProver.pop();
        assertThat(copiedProver.isUnsat()).isFalse();
        copiedProver.pop();
        assertThat(copiedProver.isUnsat()).isFalse();

        // Test that the initial prover is unaffected
        assertThat(prover.isUnsat()).isTrue();
      }
    }
  }
}
