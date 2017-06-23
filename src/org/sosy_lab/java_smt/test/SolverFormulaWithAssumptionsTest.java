/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

@RunWith(Parameterized.class)
public class SolverFormulaWithAssumptionsTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
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
      assertThat(env.getInterpolant(Collections.singletonList(firstPartForInterpolant)).toString())
          .doesNotContain("suffix");
      assertThat(
              env.isUnsatWithAssumptions(
                  ImmutableList.of(bmgr.not(suffix1), bmgr.not(suffix3), suffix2)))
          .isTrue();
      assertThat(env.getInterpolant(Collections.singletonList(firstPartForInterpolant)).toString())
          .doesNotContain("suffix");
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public <T> void assumptionsTest()
      throws SolverException, InterruptedException, InvalidConfigurationException {
    requireInterpolation();

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
          BooleanFormula itp = env.getInterpolant(Collections.singletonList(ids.get(j)));
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
}
