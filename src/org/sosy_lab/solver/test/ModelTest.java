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

import com.google.common.collect.ImmutableList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;
import org.sosy_lab.solver.api.UfDeclaration;

import java.math.BigInteger;

/**
 * Test that values from models are appropriately parsed.
 */
@RunWith(Parameterized.class)
public class ModelTest extends SolverBasedTest0 {

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

  @Test
  public void testGetSmallIntegers() throws Exception {
    testModelGetters(imgr.makeVariable("x"), imgr.makeNumber(10), BigInteger.valueOf(10), "x");
  }

  @Test
  public void testGetNegativeIntegers() throws Exception {
    testModelGetters(imgr.makeVariable("x"), imgr.makeNumber(-10), BigInteger.valueOf(-10), "x");
  }

  @Test
  public void testGetLargeIntegers() throws Exception {
    BigInteger large = new BigInteger("1000000000000000000000000000000000000000");
    testModelGetters(imgr.makeVariable("x"), imgr.makeNumber(large), large, "x");
  }

  @Test
  public void testGetSmallIntegralRationals() throws Exception {
    requireRationals();
    assert rmgr != null;
    testModelGetters(rmgr.makeVariable("x"), rmgr.makeNumber(1), Rational.ONE, "x");
  }

  @Test
  public void testGetLargeIntegralRationals() throws Exception {
    requireRationals();
    assert rmgr != null;
    BigInteger large = new BigInteger("1000000000000000000000000000000000000000");
    testModelGetters(
        rmgr.makeVariable("x"), rmgr.makeNumber(large), Rational.ofBigInteger(large), "x");
  }

  @Test
  public void testGetRationals() throws Exception {
    requireRationals();
    assert rmgr != null;
    testModelGetters(
        rmgr.makeVariable("x"),
        rmgr.makeNumber(Rational.ofString("1/3")),
        Rational.ofString("1/3"),
        "x");
  }

  @Test
  public void testGetBooleans() throws Exception {
    testModelGetters(bmgr.makeVariable("x"), bmgr.makeBoolean(true), true, "x");
  }

  @Test
  public void testGetUFs() throws Exception {
    IntegerFormula x =
        fmgr.declareAndCallUninterpretedFunction(
            "UF", FormulaType.IntegerType, ImmutableList.<Formula>of(imgr.makeVariable("arg")));
    testModelGetters(x, imgr.makeNumber(1), BigInteger.ONE, "UF");
  }

  @Test
  public void testGetMultipleUFs() throws Exception {
    IntegerFormula arg1 = imgr.makeVariable("arg1");
    IntegerFormula arg2 = imgr.makeVariable("arg2");
    UfDeclaration<IntegerFormula> declaration =
        fmgr.declareUninterpretedFunction("UF", FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula app1 = fmgr.callUninterpretedFunction(declaration, arg1);
    IntegerFormula app2 = fmgr.callUninterpretedFunction(declaration, arg2);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(app1, imgr.makeNumber(1)));
      prover.push(imgr.equal(app2, imgr.makeNumber(2)));
      prover.push(imgr.equal(arg1, imgr.makeNumber(3)));
      prover.push(imgr.equal(arg2, imgr.makeNumber(4)));

      assertThatEnvironment(prover).isSatisfiable();
      Model m = prover.getModel();

      assertThat(m.evaluate(app1)).isEqualTo(BigInteger.ONE);
      assertThat(m.evaluate(app2)).isEqualTo(BigInteger.valueOf(2));
      assertThat(m)
          .containsExactly(
              new ValueAssignment(arg1, "arg1", BigInteger.valueOf(3), ImmutableList.of()),
              new ValueAssignment(arg1, "arg2", BigInteger.valueOf(4), ImmutableList.of()),
              new ValueAssignment(
                  fmgr.callUninterpretedFunction(declaration, imgr.makeNumber(3)),
                  "UF",
                  BigInteger.valueOf(1),
                  ImmutableList.of(BigInteger.valueOf(3))),
              new ValueAssignment(
                  fmgr.callUninterpretedFunction(declaration, imgr.makeNumber(4)),
                  "UF",
                  BigInteger.valueOf(2),
                  ImmutableList.of(BigInteger.valueOf(4))));
    }
  }

  @Test
  public void testGetBitvectors() throws Exception {
    requireBitvectors();

    testModelGetters(
        bvmgr.makeVariable(1, "x"), bvmgr.makeBitvector(1, BigInteger.ONE), BigInteger.ONE, "x");
  }

  @Test
  public void testGetArrays() throws Exception {
    requireArrays();

    ArrayFormula<IntegerFormula, IntegerFormula> array =
        amgr.makeArray("array", FormulaType.IntegerType, FormulaType.IntegerType);
    ArrayFormula<IntegerFormula, IntegerFormula> updated =
        amgr.store(array, imgr.makeNumber(1), imgr.makeNumber(1));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(amgr.select(updated, imgr.makeNumber(1)), imgr.makeNumber(1)));

      assertThatEnvironment(prover).isSatisfiable();
      Model m = prover.getModel();

      for (ValueAssignment assignment : m) {
        // Check that we can iterate through with no crashes.
      }
    }
  }

  private void testModelGetters(
      Formula variable, Formula value, Object expectedValue, String varName) throws Exception {

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(mgr.makeEqual(value, variable));
      assertThatEnvironment(prover).isSatisfiable();
      Model m = prover.getModel();
      assertThat(m.evaluate(variable)).isEqualTo(expectedValue);
      boolean found = false;
      for (ValueAssignment assignment : m) {
        if (assignment.getName().equals(varName)) {
          found = true;
          assertThat(assignment.getValue()).isEqualTo(expectedValue);
        }
      }
      assertThat(found).isTrue();
    }
  }
}
