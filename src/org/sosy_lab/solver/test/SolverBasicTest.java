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
import static org.sosy_lab.solver.SolverContextFactory.Solvers.PRINCESS;
import static org.sosy_lab.solver.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;
import static org.sosy_lab.solver.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS;

import com.google.common.base.Optional;
import com.google.common.collect.ImmutableList;
import com.google.common.testing.EqualsTester;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.ProverEnvironment;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

@RunWith(Parameterized.class)
public class SolverBasicTest extends SolverBasedTest0 {

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
  public void formulaEqualsAndHashCode() {
    FunctionDeclaration<IntegerFormula> f_b =
        fmgr.declareUF("f_b", FormulaType.IntegerType, FormulaType.IntegerType);

    new EqualsTester()
        .addEqualityGroup(bmgr.makeBoolean(true))
        .addEqualityGroup(bmgr.makeBoolean(false))
        .addEqualityGroup(bmgr.makeVariable("bool_a"))
        .addEqualityGroup(imgr.makeVariable("int_a"))

        // Way of creating numbers should not make a difference.
        .addEqualityGroup(
            imgr.makeNumber(0.0),
            imgr.makeNumber(0L),
            imgr.makeNumber(BigInteger.ZERO),
            imgr.makeNumber(BigDecimal.ZERO),
            imgr.makeNumber("0"))
        .addEqualityGroup(
            imgr.makeNumber(1.0),
            imgr.makeNumber(1L),
            imgr.makeNumber(BigInteger.ONE),
            imgr.makeNumber(BigDecimal.ONE),
            imgr.makeNumber("1"))

        // The same formula when created twice should compare equal.
        .addEqualityGroup(bmgr.makeVariable("bool_b"), bmgr.makeVariable("bool_b"))
        .addEqualityGroup(
            bmgr.and(bmgr.makeVariable("bool_a"), bmgr.makeVariable("bool_b")),
            bmgr.and(bmgr.makeVariable("bool_a"), bmgr.makeVariable("bool_b")))
        .addEqualityGroup(
            imgr.equal(imgr.makeNumber(0), imgr.makeVariable("int_a")),
            imgr.equal(imgr.makeNumber(0), imgr.makeVariable("int_a")))

        // Not all solvers normalize formulas, thus the following does not hold
        // (and it is not strictly required to hold):
        //.addEqualityGroup(bmgr.and(bmgr.makeVariable("bool_c"), bmgr.makeVariable("bool_d")),
        //                  bmgr.and(bmgr.makeVariable("bool_d"), bmgr.makeVariable("bool_c")))
        //.addEqualityGroup(imgr.equal(imgr.makeNumber(0), imgr.makeVariable("int_b")),
        //                  imgr.equal(imgr.makeVariable("int_b"), imgr.makeNumber(0)))

        // UninterpretedFunctionDeclarations should not compare equal to Formulas,
        // but declaring one twice needs to return the same UIF.
        .addEqualityGroup(
            fmgr.declareUF("f_a", FormulaType.IntegerType, FormulaType.IntegerType),
            fmgr.declareUF("f_a", FormulaType.IntegerType, FormulaType.IntegerType))
        .addEqualityGroup(f_b)
        .addEqualityGroup(fmgr.callUF(f_b, ImmutableList.of(imgr.makeNumber(0))))
        .addEqualityGroup(
            fmgr.callUF(f_b, ImmutableList.of(imgr.makeNumber(1))),
            fmgr.callUF(f_b, ImmutableList.of(imgr.makeNumber(1))))
        .testEquals();
  }

  @Test
  public void variableNameExtractorTest() throws Exception {
    BooleanFormula constr =
        bmgr.or(
            imgr.equal(
                imgr.subtract(
                    imgr.add(imgr.makeVariable("x"), imgr.makeVariable("z")), imgr.makeNumber(10)),
                imgr.makeVariable("y")),
            imgr.equal(imgr.makeVariable("xx"), imgr.makeVariable("zz")));
    assertThat(mgr.extractVariables(constr).keySet()).containsExactly("x", "y", "z", "xx", "zz");
    assertThat(mgr.extractVariablesAndUFs(constr)).isEqualTo(mgr.extractVariables(constr));
  }

  @Test
  public void ufNameExtractorTest() throws Exception {
    BooleanFormula constraint =
        imgr.equal(
            fmgr.declareAndCallUF(
                "uf1", FormulaType.IntegerType, ImmutableList.<Formula>of(imgr.makeVariable("x"))),
            fmgr.declareAndCallUF(
                "uf2", FormulaType.IntegerType, ImmutableList.<Formula>of(imgr.makeVariable("y"))));

    assertThat(mgr.extractVariablesAndUFs(constraint).keySet())
        .containsExactly("uf1", "uf2", "x", "y");

    assertThat(mgr.extractVariables(constraint).keySet()).containsExactly("x", "y");
  }

  @Test
  public void assumptionsTest() throws Exception {
    BooleanFormula b = bmgr.makeVariable("b");

    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      pe.addConstraint(bmgr.or(b, bmgr.makeBoolean(false)));
      assertThat(pe.isUnsat()).isFalse();
      assertThat(pe.isUnsatWithAssumptions(ImmutableList.of(bmgr.not(b)))).isTrue();
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
