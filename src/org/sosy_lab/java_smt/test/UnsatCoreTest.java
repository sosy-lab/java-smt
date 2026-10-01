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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class UnsatCoreTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // Tests that unsat cores can not be requested after changes to the stack have been made after
  // UNSAT has been established.
  @Test
  public void getUnsatCoreAfterStackModificationFailureTest()
      throws InterruptedException, SolverException {
    requireUnsatCore();
    try (var prover = context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      prover.addConstraint(a);
      prover.addConstraint(bmgr.not(a));
      assertThat(prover.isUnsat()).isTrue();
      prover.push();
      assertThrows(IllegalStateException.class, prover::getUnsatCore);
      assertThat(prover.isUnsat()).isTrue();
      prover.pop();
      assertThrows(IllegalStateException.class, prover::getUnsatCore);
      assertThat(prover.isUnsat()).isTrue();
      prover.addConstraint(bmgr.xor(a, b));
      assertThrows(IllegalStateException.class, prover::getUnsatCore);
    }
  }

  @Test
  public void simpleGetUnsatCoreTest() throws InterruptedException, SolverException {
    requireUnsatCore();
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
  public void getUnsatCoreThrowsWithoutOptionTest() throws InterruptedException, SolverException {
    requireUnsatCore();
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
  public void simpleUnsatCoreOverAssumptionsTest() throws InterruptedException, SolverException {
    requireUnsatCoreOverAssumptions();
    // MathSat and old Z3 only allow literals as assumptions:
    assume().that(solver).isNoneOf(Solvers.MATHSAT5, Solvers.Z3_WITH_INTERPOLATION);
    try (var prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      assertThat(prover.isUnsat()).isFalse();
      var assumptions = ImmutableSet.of(a, bmgr.not(a), bmgr.xor(a, b));
      assertThat(prover.isUnsatWithAssumptions(assumptions)).isTrue();
      assertThat(prover.unsatCoreOverAssumptions(assumptions).orElseThrow())
          .containsExactly(a, bmgr.not(a));
    }
  }

  @Test
  public void unsatCoreOverAssumptionsOnlyLiteralsTest()
      throws InterruptedException, SolverException {
    requireUnsatCoreOverAssumptions();
    try (var prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      var a = bmgr.makeVariable("a");
      var b = bmgr.makeVariable("b");
      prover.addConstraint(bmgr.xor(a, b));
      assertThat(prover.isUnsat()).isFalse();
      var assumptions = ImmutableSet.of(a, b);
      assertThat(prover.isUnsatWithAssumptions(assumptions)).isTrue();
      assertThat(prover.unsatCoreOverAssumptions(assumptions).orElseThrow()).containsExactly(a, b);
    }
  }

  @Test
  public void unsatCoreOverAssumptionsThrowsForMissingOptionTest()
      throws InterruptedException, SolverException {
    requireUnsatCoreOverAssumptions();
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

  @Test
  public void unsatCoreZ3Test() throws InterruptedException, SolverException {
    requireUnsatCoreOverAssumptions();

    // FIXME Yices also has issues when options for unsat-core and unsat-assumptions are combined
    assume().that(solver).isNotEqualTo(Solvers.YICES2);

    var varA = bmgr.makeVariable("A");
    var varB = bmgr.makeVariable("B");

    try (var prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS,
            SolverContext.ProverOptions.GENERATE_UNSAT_CORE)) {
      prover.addConstraint(bmgr.xor(varA, varB));

      var core = prover.unsatCoreOverAssumptions(ImmutableList.of(varA, varB)).get();
      assertThat(core).containsExactly(varA, varB);
    }
  }

  @Test
  public void unsatCoreZ3ModelTest() throws SolverException, InterruptedException {
    requireUnsatCore();
    requireIntegers();

    var var1 = imgr.makeVariable("v");
    try (var prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS,
            SolverContext.ProverOptions.GENERATE_UNSAT_CORE)) {
      prover.addConstraint(imgr.equal(var1, imgr.makeNumber(0)));
      assertThat(prover.isUnsat()).isFalse();

      try (var model = prover.getModel()) {
        assertThat(model.asList().stream().map(Model.ValueAssignment::getName).toList())
            .containsExactly("v");
      }
    }
  }
}
