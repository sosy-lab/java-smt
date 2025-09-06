// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.collect.ImmutableList.toImmutableList;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.util.List;
import java.util.function.Supplier;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

@RunWith(Parameterized.class)
public class NonLinearArithmeticTest<T extends NumeralFormula> extends SolverBasedTest0 {

  // Boolector, CVC4, SMTInterpol, MathSAT5 and OpenSMT do not fully support non-linear arithmetic
  // (though SMTInterpol and MathSAT5 support some parts)

  // INFO: OpenSmt does not suport nonlinear arithmetic
  static final ImmutableSet<Solvers> SOLVER_WITHOUT_NONLINEAR_ARITHMETIC =
      ImmutableSet.of(
          Solvers.SMTINTERPOL,
          Solvers.MATHSAT5,
          Solvers.BOOLECTOR,
          Solvers.CVC4,
          Solvers.YICES2,
          Solvers.OPENSMT);

  @Parameters(name = "{0} {1} {2}")
  public static Iterable<Object[]> getAllSolversAndTheories() {
    return Lists.cartesianProduct(
            ImmutableList.copyOf(ParameterizedSolverBasedTest0.getAllSolvers()),
            ImmutableList.of(FormulaType.IntegerType, FormulaType.RationalType),
            ImmutableList.copyOf(NonLinearArithmetic.values()))
        .stream()
        .map(List::toArray)
        .collect(toImmutableList());
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Parameter(1)
  public FormulaType<?> formulaType;

  private NumeralFormulaManager<T, T> nmgr;

  @SuppressWarnings("unchecked")
  @Before
  public void chooseNumeralFormulaManager() {
    if (formulaType.isIntegerType()) {
      requireIntegers();
      nmgr = (NumeralFormulaManager<T, T>) imgr;
    } else if (formulaType.isRationalType()) {
      requireRationals();
      nmgr = (NumeralFormulaManager<T, T>) rmgr;
    } else {
      throw new AssertionError();
    }
  }

  @Parameter(2)
  public NonLinearArithmetic nonLinearArithmetic;

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    return super.createTestConfigBuilder()
        .setOption("solver.nonLinearArithmetic", nonLinearArithmetic.name());
  }

  private T handleExpectedException(Supplier<T> supplier) {
    try {
      return supplier.get();
    } catch (UnsupportedOperationException e) {
      if (nonLinearArithmetic == NonLinearArithmetic.USE
          && SOLVER_WITHOUT_NONLINEAR_ARITHMETIC.contains(solver)) {
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
            && !SOLVER_WITHOUT_NONLINEAR_ARITHMETIC.contains(solver))) {
      assertThatFormula(f).isUnsatisfiable();
    } else {
      assertThatFormula(f).isSatisfiable();
    }
  }

  @Test
  public void testLinearMultiplication() throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(a, nmgr.multiply(nmgr.makeNumber(2), nmgr.makeNumber(3))),
            nmgr.equal(nmgr.makeNumber(2 * 3 * 5), nmgr.multiply(a, nmgr.makeNumber(5))),
            nmgr.equal(nmgr.makeNumber(2 * 3 * 5), nmgr.multiply(nmgr.makeNumber(5), a)));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testLinearMultiplicationWithConstantUnsatisfiable()
      throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(a, nmgr.multiply(nmgr.makeNumber(2), nmgr.makeNumber(3))),
            bmgr.xor(
                nmgr.equal(nmgr.makeNumber(2 * 3 * 5), nmgr.multiply(a, nmgr.makeNumber(5))),
                nmgr.equal(nmgr.makeNumber(2 * 3 * 5), nmgr.multiply(nmgr.makeNumber(5), a))));

    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testMultiplicationOfVariables() throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");
    T b = nmgr.makeVariable("b");
    T c = nmgr.makeVariable("c");

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(c, handleExpectedException(() -> nmgr.multiply(a, b))),
            nmgr.equal(c, nmgr.makeNumber(2 * 3)));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testMultiplicationOfVariablesUnsatisfiable()
      throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");
    T b = nmgr.makeVariable("b");
    T c = nmgr.makeVariable("c");

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(handleExpectedException(() -> nmgr.multiply(a, b)), c),
            nmgr.equal(a, nmgr.makeNumber(3)),
            nmgr.equal(b, nmgr.makeNumber(5)),
            bmgr.not(nmgr.equal(c, nmgr.makeNumber(15))));

    if (solver == Solvers.MATHSAT5
        && nonLinearArithmetic != NonLinearArithmetic.APPROXIMATE_ALWAYS) {
      // MathSAT supports non-linear multiplication
      assertThatFormula(f).isUnsatisfiable();

    } else {
      assertExpectedUnsatifiabilityForNonLinearArithmetic(f);
    }
  }

  @Test
  public void testDivisionByConstant() throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(nmgr.makeNumber(2 * 3), a),
            nmgr.equal(nmgr.divide(a, nmgr.makeNumber(3)), nmgr.makeNumber(2)),
            nmgr.equal(nmgr.divide(a, nmgr.makeNumber(2)), nmgr.makeNumber(3)));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testDivisionByZero() throws SolverException, InterruptedException {
    // OpenSmt and Yices do not allow division by zero and throw an exception.
    assume()
        .withMessage("Solver %s does not support division by zero", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.YICES2, Solvers.OPENSMT);

    T a = nmgr.makeVariable("a");
    T b = nmgr.makeVariable("b");
    T zero = nmgr.makeNumber(0);

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(nmgr.divide(a, zero), nmgr.makeNumber(2)),
            nmgr.equal(nmgr.divide(b, zero), nmgr.makeNumber(4)));

    assertThatFormula(f).isSatisfiable();

    // Division by zero is still a function. So, if (/0 a) = b and (/0 a) = c, then b=c must hold
    BooleanFormula g =
        bmgr.and(
            nmgr.equal(nmgr.divide(a, zero), nmgr.makeNumber(2)),
            nmgr.equal(nmgr.divide(a, zero), nmgr.makeNumber(4)));

    assertThatFormula(g).isUnsatisfiable();
  }

  @Test
  public void testDivisionByConstantUnsatisfiable() throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            nmgr.equal(a, nmgr.makeNumber(2 * 3)),
            bmgr.xor(
                nmgr.equal(nmgr.divide(a, nmgr.makeNumber(3)), nmgr.makeNumber(2)),
                nmgr.equal(nmgr.divide(a, nmgr.makeNumber(2)), nmgr.makeNumber(3))));

    if (formulaType.equals(FormulaType.IntegerType)
        && nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_ALWAYS) {
      // Integer division is always non-linear due to rounding rules
      assertThatFormula(f).isSatisfiable();

    } else {
      assertThatFormula(f).isUnsatisfiable();
    }
  }

  @Test
  public void testDivision() throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");

    // (a == 2) && (3 == 6 / a)
    BooleanFormula f =
        bmgr.and(
            nmgr.equal(a, nmgr.makeNumber(2)),
            nmgr.equal(
                nmgr.makeNumber(3),
                handleExpectedException(() -> nmgr.divide(nmgr.makeNumber(2 * 3), a))));

    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testDivisionUnsatisfiable() throws SolverException, InterruptedException {
    T a = nmgr.makeVariable("a");

    BooleanFormula f =
        bmgr.and(
            bmgr.not(nmgr.equal(a, nmgr.makeNumber(2))),
            bmgr.not(nmgr.equal(a, nmgr.makeNumber(0))), // some solver produce model a=0 otherwise
            nmgr.equal(
                nmgr.makeNumber(3),
                handleExpectedException(() -> nmgr.divide(nmgr.makeNumber(2 * 3), a))));

    if (ImmutableSet.of(Solvers.MATHSAT5, Solvers.CVC4).contains(solver)
        && nonLinearArithmetic != NonLinearArithmetic.APPROXIMATE_ALWAYS) {
      // some solvers support non-linear multiplication (partially)
      assertThatFormula(f).isUnsatisfiable();

    } else {
      assertExpectedUnsatifiabilityForNonLinearArithmetic(f);
    }
  }
}
