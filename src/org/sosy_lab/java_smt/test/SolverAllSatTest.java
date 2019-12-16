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
import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BasicProverEnvironment.AllSatCallback;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

@RunWith(Parameterized.class)
public class SolverAllSatTest extends SolverBasedTest0 {

  @Parameters(name = "solver {0} with prover {1}")
  public static Iterable<Object[]> getAllSolvers() {
    List<Object[]> junitParams = new ArrayList<>();
    for (Solvers solver : Solvers.values()) {
      junitParams.add(new Object[] {solver, "normal"});
      junitParams.add(new Object[] {solver, "itp"});
      junitParams.add(new Object[] {solver, "opt"});
    }
    return junitParams;
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public String proverEnv;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  private BasicProverEnvironment<?> env;

  @Before
  public void setupEnvironment() {
    switch (proverEnv) {
      case "normal":
        env = context.newProverEnvironment(ProverOptions.GENERATE_ALL_SAT);
        break;
      case "itp":

        // TODO how can we support allsat in MathSat5-interpolation-prover?
        assume().that(solverToUse()).isNotEqualTo(Solvers.MATHSAT5);

        // CVC4 and Boolector do not support interpolation
        assume().that(solverToUse()).isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR);

        env = context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_ALL_SAT);
        break;

      case "opt":
        requireOptimization();
        env = context.newOptimizationProverEnvironment(ProverOptions.GENERATE_ALL_SAT);
        break;
      default:
        throw new AssertionError("unexpected");
    }
  }

  @After
  public void closeEnvironment() {
    if (env != null) {
      env.close();
    }
  }

  private static final String EXPECTED_RESULT = "AllSatTest_unsat";

  private static class TestAllSatCallback implements AllSatCallback<String> {

    private final List<List<BooleanFormula>> models = new ArrayList<>();

    @Override
    public void apply(List<BooleanFormula> pModel) {
      models.add(ImmutableList.copyOf(pModel));
    }

    @Override
    public String getResult() {
      return EXPECTED_RESULT;
    }
  }

  @Test
  public void allSatTest_unsat() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula a = imgr.makeVariable("i");
    IntegerFormula n1 = imgr.makeNumber(1);
    IntegerFormula n2 = imgr.makeNumber(2);

    BooleanFormula cond1 = imgr.equal(a, n1);
    BooleanFormula cond2 = imgr.equal(a, n2);

    BooleanFormula v1 = bmgr.makeVariable("b1");
    BooleanFormula v2 = bmgr.makeVariable("b2");

    env.push(cond1);
    env.push(cond2);

    env.push(bmgr.equivalence(v1, cond1));
    env.push(bmgr.equivalence(v2, cond2));

    TestAllSatCallback callback =
        new TestAllSatCallback() {
          @Override
          public void apply(List<BooleanFormula> pModel) {
            assert_()
                .withMessage("Formula is unsat, but all-sat callback called with model " + pModel)
                .fail();
          }
        };

    assertThat(env.allSat(callback, ImmutableList.of(v1, v2))).isEqualTo(EXPECTED_RESULT);
  }

  @Test
  public void allSatTest_xor() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula a = imgr.makeVariable("i");
    IntegerFormula n1 = imgr.makeNumber(1);
    IntegerFormula n2 = imgr.makeNumber(2);

    BooleanFormula cond1 = imgr.equal(a, n1);
    BooleanFormula cond2 = imgr.equal(a, n2);

    BooleanFormula v1 = bmgr.makeVariable("b1");
    BooleanFormula v2 = bmgr.makeVariable("b2");

    env.push(bmgr.xor(cond1, cond2));

    env.push(bmgr.equivalence(v1, cond1));
    env.push(bmgr.equivalence(v2, cond2));

    TestAllSatCallback callback = new TestAllSatCallback();

    assertThat(env.allSat(callback, ImmutableList.of(v1, v2))).isEqualTo(EXPECTED_RESULT);

    assertThat(callback.models)
        .containsExactly(ImmutableList.of(v1, bmgr.not(v2)), ImmutableList.of(bmgr.not(v1), v2));
  }

  @Test
  public void allSatTest_nondetValue() throws SolverException, InterruptedException {
    BooleanFormula v1 = bmgr.makeVariable("b1");
    BooleanFormula v2 = bmgr.makeVariable("b2");

    env.push(v1);

    TestAllSatCallback callback = new TestAllSatCallback();

    assertThat(env.allSat(callback, ImmutableList.of(v1, v2))).isEqualTo(EXPECTED_RESULT);

    assertThat(callback.models)
        .isAnyOf(
            ImmutableList.of(ImmutableList.of(v1)),
            ImmutableList.of(ImmutableList.of(v1, v2), ImmutableList.of(v1, bmgr.not(v2))),
            ImmutableList.of(ImmutableList.of(v1, bmgr.not(v2)), ImmutableList.of(v1, v2)));
  }
}
