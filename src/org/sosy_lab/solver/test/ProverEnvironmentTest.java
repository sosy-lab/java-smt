/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.solver.SolverContextFactory.Solvers.MATHSAT5;
import static org.sosy_lab.solver.SolverContextFactory.Solvers.PRINCESS;
import static org.sosy_lab.solver.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;
import static org.sosy_lab.solver.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;

import com.google.common.base.Optional;
import com.google.common.collect.ImmutableList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.ProverEnvironment;

import java.util.List;

@RunWith(Parameterized.class)
public class ProverEnvironmentTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Solvers[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void assumptionsTest() throws Exception {
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
  public void assumptionsWithModelTest() throws Exception {
    assume()
        .withFailureMessage("MathSAT can't construct models for SAT check with assumptions")
        .that(solver)
        .isNotEqualTo(MATHSAT5);
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula c = bmgr.makeVariable("c");

    try (ProverEnvironment pe = context.newProverEnvironment()) {
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
  public void unsatCoreTest() throws Exception {
    assume()
        .withFailureMessage("Princess does not support unsat core generation")
        .that(solverToUse())
        .isNotEqualTo(PRINCESS);
    try (ProverEnvironment pe = context.newProverEnvironment(GENERATE_UNSAT_CORE)) {
      pe.push();
      pe.addConstraint(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
      pe.addConstraint(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(2)));
      pe.addConstraint(imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(2)));
      assertThatEnvironment(pe).isUnsatisfiable();
      List<BooleanFormula> unsatCore = pe.getUnsatCore();
      assertThat(unsatCore)
          .containsExactly(
              imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(2)),
              imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
    }
  }

  @Test
  public void unsatCoreWithAssumptionsTest() throws Exception {
    assume()
        .withFailureMessage("Princess and Mathsat5 do not support unsat core generation")
        .that(solverToUse())
        .isNoneOf(Solvers.PRINCESS, Solvers.MATHSAT5);
    try (ProverEnvironment pe =
        context.newProverEnvironment(GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      pe.push();
      pe.addConstraint(imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(2)));
      BooleanFormula selector = bmgr.makeVariable("b");
      pe.addConstraint(bmgr.or(selector, imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(1))));
      Optional<List<BooleanFormula>> res =
          pe.unsatCoreOverAssumptions(ImmutableList.of(bmgr.not(selector)));
      assertThat(res).isPresent();
      List<BooleanFormula> unsatCore = res.get();
      assertThat(unsatCore).containsExactly(bmgr.not(selector));
    }
  }
}
