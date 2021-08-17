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

import com.google.common.collect.Collections2;
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
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** Test that we can request evaluations from models. */
@RunWith(Parameterized.class)
public class ModelEvaluationTest extends SolverBasedTest0 {

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

        // lets try to check evaluations. Actually the whole method is based on some default values
        // in the solvers, because we do not use constraints for the evaluated formulas.
        Formula eval = m.eval(formula);
        if (eval != null && solver == Solvers.SMTINTERPOL) {
          // SMTInterpol uses Rationals for model values, we use BigDecimals/Rational/BigInteger,
          // thus comparison is not directly possible and we have to use String representation
          assertThat(eval.toString())
              .isIn(Collections2.transform(possibleExpectedFormulas, f -> "" + f));
        } else {
          //          assertThat(eval).isIn(possibleExpectedFormulas);
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
        Lists.newArrayList(null, BigInteger.ZERO),
        Lists.newArrayList(null, imgr.makeNumber(0)));
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
        Lists.newArrayList(null, Rational.ZERO),
        Lists.newArrayList(null, rmgr.makeNumber(0)));
  }

  @Test
  public void testGetSmallIntegralRationalsEvaluation2()
      throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.makeVariable("y"),
        Lists.newArrayList(null, Rational.ZERO),
        Lists.newArrayList(null, rmgr.makeNumber(0)));
  }

  @Test
  public void testGetRationalsEvaluation() throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("1/3"))),
        rmgr.divide(rmgr.makeVariable("y"), rmgr.makeNumber(2)),
        Lists.newArrayList(null, Rational.ZERO),
        Lists.newArrayList(null, rmgr.makeNumber(0)));
  }

  @Test
  public void testGetBooleansEvaluation() throws SolverException, InterruptedException {
    evaluateInModel(
        bmgr.makeVariable("x"),
        bmgr.makeVariable("y"),
        Lists.newArrayList(null, false),
        Lists.newArrayList(null, bmgr.makeBoolean(false)));
  }

  @Test
  public void testGetStringsEvaluation() throws SolverException, InterruptedException {
    requireStrings();
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("hello")),
        smgr.makeVariable("y"),
        Lists.newArrayList(null, "hello"),
        Lists.newArrayList(null, smgr.makeString("hello")));
  }
}
