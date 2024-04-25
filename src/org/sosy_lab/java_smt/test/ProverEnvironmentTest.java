// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth8.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.APRON;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.BOOLECTOR;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC4;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.MATHSAT5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.PRINCESS;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;
import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Optional;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class ProverEnvironmentTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void assumptionsTest() throws SolverException, InterruptedException {
    requireNonNumeralVariables();
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");

    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      pe.addConstraint(bmgr.or(b, bmgr.makeBoolean(false)));
      pe.addConstraint(c);
      assertThat(pe.isUnsat()).isFalse();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.not(b)))).isTrue();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(b))).isFalse();
    }
  }

  @Test
  public void assumptionsWithModelTest() throws SolverException, InterruptedException {
    requireNonNumeralVariables();
    assume()
        .withMessage("MathSAT can't construct models for SAT check with assumptions")
        .that(solver)
        .isNotEqualTo(MATHSAT5);
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");

    try (ProverEnvironment pe = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      pe.push();
      pe.addConstraint(bmgr.or(b, bmgr.makeBoolean(false)));
      pe.addConstraint(c);
      assertThat(pe.isUnsat()).isFalse();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.not(b)))).isTrue();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(b))).isFalse();
      try (Model m = pe.getModel()) {
        assertThat(m.evaluate(c)).isTrue();
      }
    }
  }

  @Test
  public void unsatCoreTest() throws SolverException, InterruptedException {
    // Boolector and Apron do not support unsat core
    requireUnsatCore();
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment(GENERATE_UNSAT_CORE)) {
      unsatCoreTest0(pe);
    }
  }

  @Test
  public void unsatCoreTestForInterpolation() throws SolverException, InterruptedException {
    requireInterpolation();
    try (BasicProverEnvironment<?> pe =
        context.newProverEnvironmentWithInterpolation(GENERATE_UNSAT_CORE)) {
      unsatCoreTest0(pe);
    }
  }

  @Test
  public void unsatCoreTestForOptimizationProver() throws SolverException, InterruptedException {
    requireOptimization();

    // Z3 and Boolector do not implement unsat core for optimization
    assume().that(solverToUse()).isNoneOf(Z3, BOOLECTOR);

    try (BasicProverEnvironment<?> pe =
        context.newOptimizationProverEnvironment(GENERATE_UNSAT_CORE)) {
      unsatCoreTest0(pe);
    }
  }

  private void unsatCoreTest0(BasicProverEnvironment<?> pe)
      throws InterruptedException, SolverException {
    pe.push();
    pe.addConstraint(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
    pe.addConstraint(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(2)));
    pe.addConstraint(imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(2)));
    assertThat(pe).isUnsatisfiable();
    List<BooleanFormula> unsatCore = pe.getUnsatCore();
    assertThat(unsatCore)
        .containsExactly(
            imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(2)),
            imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
  }

  @Test
  public void unsatCoreWithAssumptionsNullTest() {
    assume()
        .withMessage(
            "Solver %s does not support unsat core generation over assumptions", solverToUse())
        .that(solverToUse())
        .isNoneOf(PRINCESS, BOOLECTOR, CVC4, CVC5);

    try (ProverEnvironment pe =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      assertThrows(NullPointerException.class, () -> pe.unsatCoreOverAssumptions(null));
    }
  }

  @Test
  public void unsatCoreWithAssumptionsTest() throws SolverException, InterruptedException {
    assume()
        .withMessage(
            "Solver %s does not support unsat core generation over assumptions", solverToUse())
        .that(solverToUse())
        .isNoneOf(PRINCESS, BOOLECTOR, CVC4, CVC5, APRON);
    requireNonNumeralVariables();
    try (ProverEnvironment pe =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      pe.push();
      pe.addConstraint(imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(2)));
      BooleanFormula selector = bmgr.makeVariable("b");
      pe.addConstraint(bmgr.or(selector, imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(1))));
      Optional<List<BooleanFormula>> res =
          pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.not(selector)));
      assertThat(res).isPresent();
      List<BooleanFormula> unsatCore = res.orElseThrow();
      assertThat(unsatCore).containsExactly(bmgr.not(selector));
    }
  }
}
