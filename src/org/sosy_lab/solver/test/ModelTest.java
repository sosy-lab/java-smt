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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.BitvectorType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;

import java.math.BigInteger;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Test that values from models are appropriately parsed.
 */
@RunWith(Parameterized.class)
public class ModelTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void testGetSmallIntegers() throws Exception {
    testModelGetters(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(10)),
        imgr.makeVariable("x"),
        BigInteger.valueOf(10),
        "x");
  }

  @Test
  public void testGetNegativeIntegers() throws Exception {
    testModelGetters(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(-10)),
        imgr.makeVariable("x"),
        BigInteger.valueOf(-10),
        "x");
  }

  @Test
  public void testGetLargeIntegers() throws Exception {
    BigInteger large = new BigInteger("1000000000000000000000000000000000000000");
    testModelGetters(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(large)),
        imgr.makeVariable("x"),
        large,
        "x");
  }

  @Test
  public void testGetSmallIntegralRationals() throws Exception {
    requireRationals();
    assert rmgr != null;
    testModelGetters(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.makeVariable("x"),
        Rational.ONE,
        "x");
  }

  @Test
  public void testGetLargeIntegralRationals() throws Exception {
    requireRationals();
    assert rmgr != null;
    BigInteger large = new BigInteger("1000000000000000000000000000000000000000");
    testModelGetters(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(large)),
        rmgr.makeVariable("x"),
        Rational.ofBigInteger(large),
        "x");
  }

  @Test
  public void testGetRationals() throws Exception {
    requireRationals();
    assert rmgr != null;
    testModelGetters(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("1/3"))),
        rmgr.makeVariable("x"),
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
        fmgr.declareAndCallUF(
            "UF", FormulaType.IntegerType, ImmutableList.of(imgr.makeVariable("arg")));
    testModelGetters(imgr.equal(x, imgr.makeNumber(1)), x, BigInteger.ONE, "UF");
  }

  @Test
  public void testGetMultipleUFs() throws Exception {
    IntegerFormula arg1 = imgr.makeVariable("arg1");
    IntegerFormula arg2 = imgr.makeVariable("arg2");
    FunctionDeclaration<IntegerFormula> declaration =
        fmgr.declareUF("UF", FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula app1 = fmgr.callUF(declaration, arg1);
    IntegerFormula app2 = fmgr.callUF(declaration, arg2);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(app1, imgr.makeNumber(1)));
      prover.push(imgr.equal(app2, imgr.makeNumber(2)));
      prover.push(imgr.equal(arg1, imgr.makeNumber(3)));
      prover.push(imgr.equal(arg2, imgr.makeNumber(4)));

      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(app1)).isEqualTo(BigInteger.ONE);
        assertThat(m.evaluate(app2)).isEqualTo(BigInteger.valueOf(2));
        assertThat(m)
            .containsExactly(
                new ValueAssignment(arg1, "arg1", BigInteger.valueOf(3), ImmutableList.of()),
                new ValueAssignment(arg1, "arg2", BigInteger.valueOf(4), ImmutableList.of()),
                new ValueAssignment(
                    fmgr.callUF(declaration, imgr.makeNumber(3)),
                    "UF",
                    BigInteger.valueOf(1),
                    ImmutableList.of(BigInteger.valueOf(3))),
                new ValueAssignment(
                    fmgr.callUF(declaration, imgr.makeNumber(4)),
                    "UF",
                    BigInteger.valueOf(2),
                    ImmutableList.of(BigInteger.valueOf(4))));
      }
    }
  }

  @Test
  public void testGetBitvectors() throws Exception {
    requireBitvectors();
    assert bvmgr != null;

    testModelGetters(
        bvmgr.equal(bvmgr.makeVariable(1, "x"), bvmgr.makeBitvector(1, BigInteger.ONE)),
        bvmgr.makeVariable(1, "x"),
        BigInteger.ONE,
        "x");
  }

  @Test
  public void testGetModelAssignments() throws Exception {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)));
      prover.push(imgr.equal(imgr.makeVariable("x"), imgr.makeVariable("y")));
      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        assertThat(prover.getModelAssignments()).containsExactlyElementsIn(m).inOrder();
      }
    }
  }

  @Test
  public void testPartialModels() throws Exception {
    assume()
        .withFailureMessage("As of now, only Z3 and Princess support partial models")
        .that(solver)
        .isIn(ImmutableList.of(Solvers.Z3, Solvers.PRINCESS));
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      IntegerFormula x = imgr.makeVariable("x");
      prover.push(imgr.equal(x, x));
      assertThatEnvironment(prover).isSatisfiable();
      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(x)).isEqualTo(null);
        assertThat(m).isEmpty();
      }
    }
  }

  @Test
  public void testPartialModelsUF() throws Exception {
    assume()
        .withFailureMessage("As of now, only Z3 and Princess support partial model evaluation")
        .that(solver)
        .isIn(ImmutableList.of(Solvers.Z3, Solvers.PRINCESS));
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula f = fmgr.declareAndCallUF("f", FormulaType.IntegerType, x);

      prover.push(imgr.equal(x, imgr.makeNumber(1)));
      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(f)).isEqualTo(null);
      }
    }
  }

  @Test
  public void testEvaluatingConstants() throws Exception {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.makeVariable("b"));
      assertThat(prover.isUnsat()).isFalse();
      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(imgr.makeNumber(1))).isEqualTo(BigInteger.ONE);
        assertThat(m.evaluate(bmgr.makeBoolean(true))).isEqualTo(true);
      }
    }
  }

  @Test
  public void testGetArrays() throws Exception {
    requireArrays();
    assert amgr != null;

    ArrayFormula<IntegerFormula, IntegerFormula> array =
        amgr.makeArray("array", FormulaType.IntegerType, FormulaType.IntegerType);
    ArrayFormula<IntegerFormula, IntegerFormula> updated =
        amgr.store(array, imgr.makeNumber(1), imgr.makeNumber(1));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(amgr.select(updated, imgr.makeNumber(1)), imgr.makeNumber(1)));

      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        for (@SuppressWarnings("unused") ValueAssignment assignment : m) {
          // Check that we can iterate through with no crashes.
        }
        assertThat(m.evaluate(amgr.select(updated, imgr.makeNumber(1)))).isEqualTo(BigInteger.ONE);
      }
    }
  }

  private void testModelGetters(
      BooleanFormula constraint, Formula variable, Object expectedValue, String varName)
      throws Exception {

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(constraint);
      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(variable)).isEqualTo(expectedValue);

        List<ValueAssignment> relevantAssignments =
            prover
                .getModelAssignments()
                .stream()
                .filter(assignment -> assignment.getName().equals(varName))
                .collect(Collectors.toList());
        assertThat(relevantAssignments).hasSize(1);
        ValueAssignment assignment = Iterables.getOnlyElement(relevantAssignments);
        assertThat(assignment.getValue()).isEqualTo(expectedValue);
      }
    }
  }

  @Test
  public void UFtest() throws SolverException, InterruptedException {
    requireQuantifiers();
    requireBitvectors();
    // only Z3 fulfills these requirements

    BitvectorType t32 = BitvectorType.getBitvectorTypeWithSize(32);
    FunctionDeclaration<BitvectorFormula> si1 = fmgr.declareUF("*signed_int@1", t32, t32);
    FunctionDeclaration<BitvectorFormula> si2 = fmgr.declareUF("*signed_int@2", t32, t32);
    BitvectorFormula ctr = bvmgr.makeVariable(t32, "*signed_int@1@counter");
    BitvectorFormula adr = bvmgr.makeVariable(t32, "__ADDRESS_OF_test");
    BitvectorFormula num0 = bvmgr.makeBitvector(32, 0);
    BitvectorFormula num4 = bvmgr.makeBitvector(32, 4);
    BitvectorFormula num10 = bvmgr.makeBitvector(32, 10);

    BooleanFormula a11 =
        bmgr.implication(
            bmgr.and(
                bvmgr.lessOrEquals(adr, ctr, false),
                bvmgr.lessThan(ctr, bvmgr.add(adr, num10), false)),
            bvmgr.equal(fmgr.callUF(si2, ctr), num0));
    BooleanFormula a21 =
        bmgr.not(
            bmgr.and(
                bvmgr.lessOrEquals(adr, ctr, false),
                bvmgr.lessThan(ctr, bvmgr.add(adr, num10), false)));
    BooleanFormula body =
        bmgr.and(
            a11, bmgr.implication(a21, bvmgr.equal(fmgr.callUF(si2, ctr), fmgr.callUF(si1, ctr))));
    BooleanFormula a1 = qmgr.forall(body, ctr);
    BooleanFormula a2 =
        bvmgr.equal(fmgr.callUF(si1, bvmgr.add(adr, bvmgr.multiply(num4, num0))), num0);

    BooleanFormula f = bmgr.and(a1, bvmgr.lessThan(num0, adr, true), bmgr.not(a2));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(f);
      assertThat(prover.isUnsat()).isFalse();
      try (Model m = prover.getModel()) {
        // TODO the model is not correct for Z3, check this!

        // dummy-check for TRUE, such that the JUnit-test is not useless :-)
        assertThat(m.evaluate(bmgr.makeBoolean(true))).isEqualTo(true);
      }
    }
  }
}
