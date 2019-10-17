/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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

import static com.google.common.collect.ImmutableList.toImmutableList;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.util.Arrays;
import java.util.function.Supplier;
import org.junit.AssumptionViolatedException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

@RunWith(Parameterized.class)
public class NonLinearArithmeticWithModuloTest extends SolverBasedTest0 {

  @Parameters(name = "{0} {1}")
  public static Iterable<Object[]> getAllSolvers() {
    return Lists.cartesianProduct(
            Arrays.asList(Solvers.values()), Arrays.asList(NonLinearArithmetic.values()))
        .stream()
        .map(e -> e.toArray())
        .collect(toImmutableList());
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Parameter(1)
  public NonLinearArithmetic nonLinearArithmetic;

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    return super.createTestConfigBuilder()
        .setOption("solver.nonLinearArithmetic", nonLinearArithmetic.name());
  }

  private IntegerFormula handleExpectedException(Supplier<IntegerFormula> supplier) {
    try {
      return supplier.get();
    } catch (UnsupportedOperationException e) {
      if (nonLinearArithmetic == NonLinearArithmetic.USE
          && NonLinearArithmeticTest.SOLVER_WITHOUT_NONLINEAR_ARITHMETIC.contains(solver)) {
        throw new AssumptionViolatedException(
            "Expected UnsupportedOperationException was thrown correctly");
      }
      throw e;
    }
  }

  private void assertExpectedUnsatifiabilityForNonLinearArithmetic(BooleanFormula f)
      throws SolverException, InterruptedException {
    if (nonLinearArithmetic == NonLinearArithmetic.USE
        || (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK
            && !NonLinearArithmeticTest.SOLVER_WITHOUT_NONLINEAR_ARITHMETIC.contains(solver))) {
      assertThatFormula(f).isUnsatisfiable();
    } else {
      assertThatFormula(f).isSatisfiable();
    }
  }

  @Test
  public void testModuloConstant() throws SolverException, InterruptedException {
    IntegerFormula a = imgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            imgr.equal(a, imgr.makeNumber(3)),
            imgr.equal(
                imgr.makeNumber(1),
                handleExpectedException(() -> imgr.modulo(a, imgr.makeNumber(2)))));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testModuloConstantUnsatisfiable() throws SolverException, InterruptedException {
    IntegerFormula a = imgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            imgr.equal(a, imgr.makeNumber(5)),
            imgr.equal(
                imgr.makeNumber(1),
                handleExpectedException(() -> imgr.modulo(a, imgr.makeNumber(3)))));

    if (ImmutableSet.of(Solvers.SMTINTERPOL, Solvers.CVC4).contains(solver)
        && nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK) {
      // some solvers support modulo with constants
      assertThatFormula(f).isUnsatisfiable();

    } else {
      assertExpectedUnsatifiabilityForNonLinearArithmetic(f);
    }
  }

  @Test
  public void testModulo() throws SolverException, InterruptedException {
    IntegerFormula a = imgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            imgr.equal(a, imgr.makeNumber(2)),
            imgr.equal(
                imgr.makeNumber(1),
                handleExpectedException(() -> imgr.modulo(imgr.makeNumber(3), a))));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testModuloUnsatisfiable() throws SolverException, InterruptedException {
    IntegerFormula a = imgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            imgr.equal(a, imgr.makeNumber(3)),
            imgr.equal(
                imgr.makeNumber(1),
                handleExpectedException(() -> imgr.modulo(imgr.makeNumber(5), a))));

    if (Solvers.CVC4 == solver && nonLinearArithmetic != NonLinearArithmetic.APPROXIMATE_ALWAYS) {
      // some solvers support non-linear multiplication (partially)
      assertThatFormula(f).isUnsatisfiable();

    } else {
      assertExpectedUnsatifiabilityForNonLinearArithmetic(f);
    }
  }
}
