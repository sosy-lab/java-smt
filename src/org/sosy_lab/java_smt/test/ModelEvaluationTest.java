// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.Collection;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

/** Test that we can request evaluations from models. */
@RunWith(Parameterized.class)
public class ModelEvaluationTest extends SolverBasedTest0 {

  /**
   * This is the default boolean value for unknown model evaluations. For unknown model evaluation
   * for variables or formulas, the solver can return NULL or a default value.
   */
  private static final boolean DEFAULT_MODEL_BOOLEAN = false;

  /**
   * This is the default integer value for unknown model evaluations. For unknown model evaluation
   * for variables or formulas, the solver can return NULL or a default value.
   */
  private static final int DEFAULT_MODEL_INT = 0;

  /**
   * This is the default String value for unknown model evaluations. For unknown model evaluation
   * for variables or formulas, the solver can return NULL or a default value.
   */
  private static final String DEFAULT_MODEL_STRING = "";

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  private void evaluateInModel(
      BooleanFormula constraint,
      Formula formula,
      Collection<Object> possibleExpectedValues,
      Collection<Formula> possibleExpectedFormulas)
      throws SolverException, InterruptedException {

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(constraint);
      assertThat(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        if (formula instanceof BooleanFormula) {
          assertThat(m.evaluate((BooleanFormula) formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof IntegerFormula) {
          assertThat(m.evaluate((IntegerFormula) formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof RationalFormula) {
          assertThat(m.evaluate((RationalFormula) formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof StringFormula) {
          assertThat(m.evaluate((StringFormula) formula)).isIn(possibleExpectedValues);
        }

        // let's try to check evaluations. Actually the whole method is based on some default values
        // in the solvers, because we do not use constraints for the evaluated formulas.
        Formula eval = m.eval(formula);
        if (eval != null) {
          switch (solver) {
            case Z3:
              // ignore, Z3 provides arbitrary values
              break;
            case BOOLECTOR:
              // ignore, Boolector provides no useful values
              break;
            default:
              assertThat(eval).isIn(possibleExpectedFormulas);
          }
        }
      }
    }
  }

  @Test
  public void testGetSmallIntegersEvaluation1() throws SolverException, InterruptedException {
    requireIntegers();
    evaluateInModel(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(10)),
        imgr.add(imgr.makeVariable("y"), imgr.makeVariable("z")),
        Lists.newArrayList(null, BigInteger.valueOf(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, imgr.makeNumber(DEFAULT_MODEL_INT)));
  }

  @Test
  public void testGetSmallIntegersEvaluation2() throws SolverException, InterruptedException {
    requireIntegers();
    evaluateInModel(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(10)),
        imgr.add(imgr.makeVariable("y"), imgr.makeNumber(1)),
        Lists.newArrayList(null, BigInteger.ONE),
        Lists.newArrayList(null, imgr.makeNumber(1)));
  }

  @Test
  public void testGetNegativeIntegersEvaluation() throws SolverException, InterruptedException {
    requireIntegers();
    evaluateInModel(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(-10)),
        imgr.add(imgr.makeVariable("y"), imgr.makeNumber(1)),
        Lists.newArrayList(null, BigInteger.ONE),
        Lists.newArrayList(null, imgr.makeNumber(1)));
  }

  @Test
  public void testGetSmallIntegralRationalsEvaluation1()
      throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.add(rmgr.makeVariable("y"), rmgr.makeVariable("y")),
        Lists.newArrayList(null, Rational.of(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, rmgr.makeNumber(DEFAULT_MODEL_INT)));
  }

  @Test
  public void testGetSmallIntegralRationalsEvaluation2()
      throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.makeVariable("y"),
        Lists.newArrayList(null, Rational.of(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, rmgr.makeNumber(DEFAULT_MODEL_INT)));
  }

  @Test
  public void testGetRationalsEvaluation() throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("1/3"))),
        rmgr.divide(rmgr.makeVariable("y"), rmgr.makeNumber(2)),
        Lists.newArrayList(null, Rational.of(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, rmgr.makeNumber(DEFAULT_MODEL_INT)));
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("15"))),
        rmgr.makeVariable("x"),
        Lists.newArrayList(null, Rational.of(15)),
        Lists.newArrayList(null, rmgr.makeNumber(15)));
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("15"))),
        rmgr.divide(rmgr.makeVariable("x"), rmgr.makeNumber(3)),
        Lists.newArrayList(null, Rational.of(5)),
        Lists.newArrayList(null, rmgr.makeNumber(5)));
  }

  @Test
  public void testGetBooleansEvaluation() throws SolverException, InterruptedException {
    evaluateInModel(
        bmgr.makeVariable("x"),
        bmgr.makeVariable("y"),
        Lists.newArrayList(null, DEFAULT_MODEL_BOOLEAN),
        Lists.newArrayList(null, bmgr.makeBoolean(DEFAULT_MODEL_BOOLEAN)));
  }

  @Test
  public void testGetStringsEvaluation() throws SolverException, InterruptedException {
    requireStrings();
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("hello")),
        smgr.makeVariable("y"),
        Lists.newArrayList(null, DEFAULT_MODEL_STRING),
        Lists.newArrayList(null, smgr.makeString(DEFAULT_MODEL_STRING)));
  }
}
