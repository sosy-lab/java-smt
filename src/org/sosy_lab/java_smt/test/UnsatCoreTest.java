/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableSet;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class UnsatCoreTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Test
  public void test_getUnsatCore() throws InterruptedException, SolverException {
    assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);

    try (var prover = context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      prover.addConstraint(a);
      prover.addConstraint(bmgr.not(a));
      prover.addConstraint(bmgr.xor(a, b));
      assertThat(prover.isUnsat()).isTrue();
      assertThat(prover.getUnsatCore()).containsExactly(a, bmgr.not(a));
    }
  }

  @Test
  public void test_getUnsatCore_noOption() throws InterruptedException, SolverException {
    assume().that(solver).isNotEqualTo(Solvers.BOOLECTOR);

    try (var prover = context.newProverEnvironment()) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      prover.addConstraint(a);
      prover.addConstraint(bmgr.not(a));
      prover.addConstraint(bmgr.xor(a, b));
      assertThat(prover.isUnsat()).isTrue();
      assertThrows(IllegalStateException.class, prover::getUnsatCore);
    }
  }

  @Test
  public void test_unsatCoreOverAssumptions() throws InterruptedException, SolverException {
    assume()
        .that(solver)
        .isNoneOf(Solvers.OPENSMT, Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.CVC4, Solvers.CVC5);
    // MathSat and old Z3 only allow literals as assumptions:
    assume().that(solver).isNoneOf(Solvers.MATHSAT5, Solvers.Z3_WITH_INTERPOLATION);
    try (var prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      assertThat(prover.isUnsat()).isFalse();
      var assumptions = ImmutableSet.of(a, bmgr.not(a), bmgr.xor(a, b));
      assertThat(prover.isUnsatWithAssumptions(assumptions)).isTrue();
      assertThat(prover.unsatCoreOverAssumptions(assumptions).get())
          .containsExactly(a, bmgr.not(a));
    }
  }

  @Test
  public void test_unsatCoreOverAssumptions_onlyLiterals()
      throws InterruptedException, SolverException {
    assume()
        .that(solver)
        .isNoneOf(Solvers.OPENSMT, Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.CVC4, Solvers.CVC5);
    try (var prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      prover.addConstraint(bmgr.xor(a, b));
      assertThat(prover.isUnsat()).isFalse();
      var assumptions = ImmutableSet.of(a, b);
      assertThat(prover.isUnsatWithAssumptions(assumptions)).isTrue();
      assertThat(prover.unsatCoreOverAssumptions(assumptions).get()).containsExactly(a, b);
    }
  }

  @Test
  public void test_unsatCoreOverAssumptions_noOption()
      throws InterruptedException, SolverException {
    assume()
        .that(solver)
        .isNoneOf(Solvers.OPENSMT, Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.CVC4, Solvers.CVC5);
    try (var prover = context.newProverEnvironment()) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      prover.addConstraint(bmgr.xor(a, b));
      assertThat(prover.isUnsat()).isFalse();
      var assumptions = ImmutableSet.of(a, b);
      assertThat(prover.isUnsatWithAssumptions(assumptions)).isTrue();
      assertThrows(IllegalStateException.class, () -> prover.unsatCoreOverAssumptions(assumptions));
    }
  }
}
