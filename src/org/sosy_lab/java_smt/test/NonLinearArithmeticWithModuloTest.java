// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import com.google.common.collect.ImmutableSet;
import java.util.function.Supplier;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.Parameter;
import org.junit.jupiter.params.ParameterizedClass;
import org.junit.jupiter.params.provider.EnumSource;
import org.opentest4j.TestAbortedException;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

@ParameterizedClass
@EnumSource(NonLinearArithmetic.class)
public class NonLinearArithmeticWithModuloTest {
  @Parameter public NonLinearArithmetic nonLinearArithmetic;

  @Nested
  class Tests extends SolverBasedTest.ParameterizedSolverBasedTest {
    @Override
    protected ConfigurationBuilder createTestConfigBuilder() throws InvalidConfigurationException {
      return super.createTestConfigBuilder()
          .setOption("solver.nonLinearArithmetic", nonLinearArithmetic.name());
    }

    private IntegerFormula handleExpectedException(Supplier<IntegerFormula> supplier) {
      try {
        return supplier.get();
      } catch (UnsupportedOperationException e) {
        if (nonLinearArithmetic == NonLinearArithmetic.USE
            && NonLinearArithmeticTest.Solver.SOLVER_WITHOUT_NONLINEAR_ARITHMETIC.contains(
                solver)) {
          throw new TestAbortedException(
              "Expected UnsupportedOperationException was thrown correctly");
        }
        throw e;
      }
    }

    private void assertExpectedUnsatifiabilityForNonLinearArithmetic(BooleanFormula f)
        throws SolverException, InterruptedException {
      if (nonLinearArithmetic == NonLinearArithmetic.USE
          || (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK
              && !NonLinearArithmeticTest.Solver.SOLVER_WITHOUT_NONLINEAR_ARITHMETIC.contains(
                  solver))) {
        assertThatFormula(f).isUnsatisfiable();
      } else {
        assertThatFormula(f).isSatisfiable();
      }
    }

    @Test
    public void testModuloConstant() throws SolverException, InterruptedException {
      requireIntegers();
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
      requireIntegers();
      IntegerFormula a = imgr.makeVariable("a");

      BooleanFormula f =
          bmgr.and(
              imgr.equal(a, imgr.makeNumber(5)),
              imgr.equal(
                  imgr.makeNumber(1),
                  handleExpectedException(() -> imgr.modulo(a, imgr.makeNumber(3)))));

      // INFO: OpenSMT does support modulo with constants
      if (ImmutableSet.of(
                  Solvers.SMTINTERPOL,
                  Solvers.CVC4,
                  Solvers.YICES2,
                  Solvers.OPENSMT,
                  Solvers.MATHSAT5)
              .contains(solver)
          && nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK) {
        // some solvers support modulo with constants
        assertThatFormula(f).isUnsatisfiable();

      } else {
        assertExpectedUnsatifiabilityForNonLinearArithmetic(f);
      }
    }

    @Test
    public void testModulo() throws SolverException, InterruptedException {
      requireIntegers();
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
      requireIntegers();
      IntegerFormula a = imgr.makeVariable("a");

      BooleanFormula f =
          bmgr.and(
              imgr.equal(a, imgr.makeNumber(3)),
              imgr.equal(
                  imgr.makeNumber(1),
                  handleExpectedException(() -> imgr.modulo(imgr.makeNumber(5), a))));

      if (ImmutableSet.of(Solvers.CVC4, Solvers.MATHSAT5).contains(solver)
          && nonLinearArithmetic != NonLinearArithmetic.APPROXIMATE_ALWAYS) {
        // some solvers support non-linear multiplication (partially)
        assertThatFormula(f).isUnsatisfiable();

      } else {
        assertExpectedUnsatifiabilityForNonLinearArithmetic(f);
      }
    }
  }
}
