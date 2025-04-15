// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.SolverContextFactoryTest.IS_WINDOWS;

import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
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

    // INFO: OpenSmt does not allow any access after the solver has been closed
    // CVC5 does not allow any access after close()
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC5, Solvers.OPENSMT);

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

    // For CVC4 and Bitwuzla, we close the solver, however do not finalize and cleanup the terms,
    // thus direct access is possible, operations are forbidden.
    // See https://github.com/sosy-lab/java-smt/issues/169
    assume()
        .withMessage(
            "Solver %s does not support to access formulae after closing the context",
            solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.BITWUZLA);

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
  @SuppressWarnings("try")
  public void testCVC5WithValidOptions() throws InvalidConfigurationException {
    assume().that(solverToUse()).isEqualTo(Solvers.CVC5);

    var config2 =
        createTestConfigBuilder()
            .setOption("solver.cvc5.furtherOptions", "solve-bv-as-int=bitwise")
            .build();
    var factory2 = new SolverContextFactory(config2, logger, shutdownNotifierToUse());
    try (var context2 = factory2.generateContext()) {
      // create and ignore
    }
  }

  @Test(timeout = 5000)
  @SuppressWarnings({"try", "CheckReturnValue"})
  public void testCVC5WithValidOptionsTimeLimit()
      throws InvalidConfigurationException, InterruptedException {
    assume().that(solverToUse()).isEqualTo(Solvers.CVC5);
    assume()
        .withMessage("CVC5 has an issue with creating and closing a second context on Windows.")
        .that(IS_WINDOWS)
        .isFalse();

    //  tlimit-per is time limit in ms of wall clock time per query
    var configValid =
        createTestConfigBuilder().setOption("solver.cvc5.furtherOptions", "tlimit-per=1").build();
    var factoryWOption = new SolverContextFactory(configValid, logger, shutdownNotifierToUse());
    try (SolverContext contextWTimeLimit = factoryWOption.generateContext()) {
      FormulaManager fmgrTimeLimit = contextWTimeLimit.getFormulaManager();
      HardIntegerFormulaGenerator hifg =
          new HardIntegerFormulaGenerator(
              fmgrTimeLimit.getIntegerFormulaManager(), fmgrTimeLimit.getBooleanFormulaManager());
      BooleanFormula hardProblem = hifg.generate(100);
      try (ProverEnvironment proverTimeLimited = contextWTimeLimit.newProverEnvironment()) {
        proverTimeLimited.addConstraint(hardProblem);
        assertThrows(SolverException.class, proverTimeLimited::isUnsat);
      }
    }
  }

  @Test
  public void testCVC5WithInvalidOptions() throws InvalidConfigurationException {
    assume().that(solverToUse()).isEqualTo(Solvers.CVC5);

    var config2 =
        createTestConfigBuilder().setOption("solver.cvc5.furtherOptions", "foo=bar").build();
    var factory2 = new SolverContextFactory(config2, logger, shutdownNotifierToUse());
    assertThrows(InvalidConfigurationException.class, factory2::generateContext);
  }
}
