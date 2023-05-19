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

    assertThat(bmgr.isTrue(term)).isFalse();
    assertThat(bmgr.isFalse(term)).isFalse();
    assertThat(bmgr.isTrue(termTrue)).isTrue();
    assertThat(bmgr.isFalse(termFalse)).isTrue();

    // Z3 allows simple checks (comparison against constants like TRUE/FALSE), lets abort here.
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

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
}
