// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

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
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

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

  // INFO: OpenSmt only support interpolation for QF_LIA, QF_LRA and QF_UF
  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  private BasicProverEnvironment<?> env;

  @Before
  public void setupEnvironment() {
    assume().that(solverToUse()).isNotEqualTo(Solvers.SOLVERLESS);
    switch (proverEnv) {
      case "normal":
        env = context.newProverEnvironment(ProverOptions.GENERATE_ALL_SAT);
        break;
      case "itp":
        requireInterpolation();

        // TODO how can we support allsat in MathSat5-interpolation-prover?
        assume().that(solverToUse()).isNotEqualTo(Solvers.MATHSAT5);

        // CVC4 and Boolector do not support interpolation
        assume().that(solverToUse()).isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR, Solvers.Z3);

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

    // ((i=1) XOR (i=2)) & b1 <=> (i=1) & b2 <=> (i=2)
    // query ALLSAT for predicates [b1, b2] --> {[b1,-b2], [-b1,b2]}

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

  @Test
  public void allSatTest_withQuantifier() throws SolverException, InterruptedException {
    requireBitvectors();
    requireQuantifiers();

    assume()
        .withMessage("solver does only partially support quantifiers")
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);

    if ("opt".equals(proverEnv)) {
      assume()
          .withMessage("solver reports a partial model when using optimization")
          .that(solverToUse())
          .isNotEqualTo(Solvers.Z3);
    }

    if ("itp".equals(proverEnv)) {
      assume()
          .withMessage("solver reports a inconclusive sat-check when using interpolation")
          .that(solverToUse())
          .isNotEqualTo(Solvers.PRINCESS);
    }

    // (y = 1)
    // & (PRED1 <-> (y = 1))
    // & (PRED3 <-> ALL x_0. (3 * x_0 != y))
    // query ALLSAT for predicates [PRED1, PRED3] --> {[PRED1, -PRED3]}

    // ugly detail in bitvector theory: 2863311531*3=1 mod 2^32,
    // thus the quantified part from above is FALSE.

    int bitsize = 32;
    BitvectorFormula y = bvmgr.makeVariable(bitsize, "y");
    BitvectorFormula one = bvmgr.makeBitvector(bitsize, 1);
    BitvectorFormula three = bvmgr.makeBitvector(bitsize, 3);
    BitvectorFormula bound = bvmgr.makeVariable(bitsize, "x_0");
    BooleanFormula pred1 = bmgr.makeVariable("pred1");
    BooleanFormula pred3 = bmgr.makeVariable("pred3");

    BooleanFormula query =
        bmgr.and(
            bvmgr.equal(y, one),
            bmgr.equivalence(pred1, bvmgr.equal(y, one)),
            bmgr.equivalence(
                pred3,
                qmgr.forall(
                    ImmutableList.of(bound),
                    bmgr.not(bvmgr.equal(y, bvmgr.multiply(three, bound))))));

    env.push(query);

    assertThat(env.isUnsat()).isFalse();

    TestAllSatCallback callback = new TestAllSatCallback();

    assertThat(env.allSat(callback, ImmutableList.of(pred1, pred3))).isEqualTo(EXPECTED_RESULT);

    assertThat(callback.models)
        .isEqualTo(ImmutableList.of(ImmutableList.of(pred1, bmgr.not(pred3))));
  }
}
