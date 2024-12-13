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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedInterpolatingSolverBasedTest0;

public class InterpolatingSolverFormulaWithAssumptionsTest
    extends ParameterizedInterpolatingSolverBasedTest0 {

  // INFO: OpenSmt only support interpolation for QF_LIA, QF_LRA and QF_UF
  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  /**
   * Generate a prover environment depending on the parameter above. Can be overridden to
   * parameterize the test.
   *
   * @throws InvalidConfigurationException overriding methods are allowed to throw this
   */
  @SuppressWarnings({"unchecked", "rawtypes", "CheckReturnValue"})
  protected <T> InterpolatingProverEnvironment<T> newEnvironmentForTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {

    // check if we support assumption-solving
    try (InterpolatingProverEnvironment<?> env = context.newProverEnvironmentWithInterpolation()) {
      env.isUnsatWithAssumptions(ImmutableList.of());
    } catch (UnsupportedOperationException e) {
      assume()
          .withMessage("Solver %s does not support assumption-solving", solverToUse())
          .that(e)
          .isNull();
    }

    return (InterpolatingProverEnvironment<T>) context.newProverEnvironmentWithInterpolation();
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public <T> void basicAssumptionsTest()
      throws SolverException, InterruptedException, InvalidConfigurationException {
    requireInterpolation();

    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    IntegerFormula v1 = imgr.makeVariable("v1");
    IntegerFormula v2 = imgr.makeVariable("v2");

    BooleanFormula suffix1 = bmgr.makeVariable("suffix1");
    BooleanFormula suffix2 = bmgr.makeVariable("suffix2");
    BooleanFormula suffix3 = bmgr.makeVariable("suffix3");

    BooleanFormula term1 =
        bmgr.or(
            bmgr.and(imgr.equal(v1, imgr.makeNumber(BigDecimal.ONE)), bmgr.not(imgr.equal(v1, v2))),
            suffix1);
    BooleanFormula term2 = bmgr.or(imgr.equal(v2, imgr.makeNumber(BigDecimal.ONE)), suffix2);
    BooleanFormula term3 =
        bmgr.or(bmgr.not(imgr.equal(v1, imgr.makeNumber(BigDecimal.ONE))), suffix3);

    try (InterpolatingProverEnvironment<T> env = newEnvironmentForTest()) {

      T firstPartForInterpolant = env.push(term1);
      env.push(term2);
      env.push(term3);

      assertThat(
              env.isUnsatWithAssumptions(
                  ImmutableList.of(bmgr.not(suffix1), bmgr.not(suffix2), suffix3)))
          .isTrue();
      assertThat(env.getInterpolant(ImmutableList.of(firstPartForInterpolant)).toString())
          .doesNotContain("suffix");
      assertThat(
              env.isUnsatWithAssumptions(
                  ImmutableList.of(bmgr.not(suffix1), bmgr.not(suffix3), suffix2)))
          .isTrue();
      assertThat(env.getInterpolant(ImmutableList.of(firstPartForInterpolant)).toString())
          .doesNotContain("suffix");
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public <T> void assumptionsTest()
      throws SolverException, InterruptedException, InvalidConfigurationException {
    requireInterpolation();

    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    int n = 5;

    IntegerFormula x = imgr.makeVariable("x");
    List<BooleanFormula> assignments = new ArrayList<>();
    List<BooleanFormula> suffices = new ArrayList<>();
    List<BooleanFormula> terms = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      BooleanFormula a = imgr.equal(x, imgr.makeNumber(i));
      BooleanFormula suffix = bmgr.makeVariable("suffix" + i);
      assignments.add(a);
      suffices.add(suffix);
      terms.add(bmgr.or(a, suffix));
    }

    List<BooleanFormula> toCheckSat = new ArrayList<>();
    List<BooleanFormula> toCheckUnsat = new ArrayList<>();

    for (int i = 2; i < n; i++) {
      try (InterpolatingProverEnvironment<T> env = newEnvironmentForTest()) {

        List<T> ids = new ArrayList<>();
        for (int j = 0; j < i; j++) {
          ids.add(env.push(terms.get(j)));
        }

        // x==1 && x==2 ...
        assertThat(
                env.isUnsatWithAssumptions(Lists.transform(suffices.subList(0, i + 1), bmgr::not)))
            .isTrue();

        for (int j = 0; j < i; j++) {
          BooleanFormula itp = env.getInterpolant(ImmutableList.of(ids.get(j)));
          for (String var : mgr.extractVariables(itp).keySet()) {
            assertThat(var).doesNotContain("suffix");
          }
          BooleanFormula contra = itp;
          for (int k = 0; k < i; k++) {
            if (k != j) {
              contra = bmgr.and(contra, assignments.get(k));
            }
          }
          toCheckSat.add(bmgr.implication(assignments.get(j), itp));
          toCheckUnsat.add(contra);
        }
      }

      for (BooleanFormula f : toCheckSat) {
        assertThatFormula(f).isSatisfiable();
      }

      for (BooleanFormula f : toCheckUnsat) {
        assertThatFormula(f).isUnsatisfiable();
      }
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void assumptionsTest1() throws SolverException, InterruptedException {
    /*
    (declare-fun A () Bool)
    (push 1)
    (check-sat-assumptions (A))
    (assert (not A))
    (check-sat-assumptions (A))
    */

    BooleanFormula a = bmgr.makeVariable("a");
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      assertThat(pe.isUnsatWithAssumptions(ImmutableSet.of(a))).isFalse();
      pe.addConstraint(bmgr.not(a));
      assertThat(pe.isUnsatWithAssumptions(ImmutableSet.of(a))).isTrue();
    }
  }
}
