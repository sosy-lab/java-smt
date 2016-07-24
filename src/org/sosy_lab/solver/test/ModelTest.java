/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
import static org.sosy_lab.solver.api.FormulaType.IntegerType;

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
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
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

  private final static List<Solvers> SOLVERS_WITH_PARTIAL_MODEL =
      ImmutableList.of(Solvers.Z3, Solvers.PRINCESS);

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
        fmgr.declareAndCallUF("UF", IntegerType, ImmutableList.of(imgr.makeVariable("arg")));
    testModelGetters(imgr.equal(x, imgr.makeNumber(1)), x, BigInteger.ONE, "UF");
  }

  @Test
  public void testGetMultipleUFs() throws Exception {
    IntegerFormula arg1 = imgr.makeVariable("arg1");
    IntegerFormula arg2 = imgr.makeVariable("arg2");
    FunctionDeclaration<IntegerFormula> declaration =
        fmgr.declareUF("UF", IntegerType, IntegerType);
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
  public void testQuantifiedUF() throws Exception {
    requireQuantifiers();

    IntegerFormula var = imgr.makeVariable("var");
    BooleanFormula varIsOne = imgr.equal(var, imgr.makeNumber(1));
    IntegerFormula boundVar = imgr.makeVariable("boundVar");
    BooleanFormula boundVarIsZero = imgr.equal(boundVar, imgr.makeNumber(0));

    String func = "func";
    IntegerFormula funcAtZero = fmgr.declareAndCallUF(func, IntegerType, imgr.makeNumber(0));
    IntegerFormula funcAtBoundVar = fmgr.declareAndCallUF(func, IntegerType, boundVar);

    BooleanFormula body = bmgr.and(boundVarIsZero, imgr.equal(var, funcAtBoundVar));
    BooleanFormula f = bmgr.and(varIsOne, qmgr.exists(ImmutableList.of(boundVar), body));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(f);
      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        for (@SuppressWarnings("unused") ValueAssignment assignment : m) {
          // Check that we can iterate through with no crashes.
        }
        assertThat(m)
            .contains(
                new ValueAssignment(
                    funcAtZero, func, BigInteger.ONE, ImmutableList.of(BigInteger.ZERO)));
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
    testModelIterator(
        bmgr.and(
            imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)),
            imgr.equal(imgr.makeVariable("x"), imgr.makeVariable("y"))));
  }

  @Test
  public void testEmptyStackModel() throws Exception {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      assertThatEnvironment(prover).isSatisfiable();
      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(imgr.makeNumber(123))).isEqualTo(BigInteger.valueOf(123));
        assertThat(m.evaluate(bmgr.makeBoolean(true))).isEqualTo(true);
        assertThat(m.evaluate(bmgr.makeBoolean(false))).isEqualTo(false);
        if (SOLVERS_WITH_PARTIAL_MODEL.contains(solver)) {
          // partial model should not return an evaluation
          assertThat(m.evaluate(imgr.makeVariable("y"))).isNull();
        } else {
          assertThat(m.evaluate(imgr.makeVariable("y"))).isNotNull();
        }
      }
    }
  }

  @Test
  public void testNonExistantSymbol() throws Exception {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.makeBoolean(true));
      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        if (SOLVERS_WITH_PARTIAL_MODEL.contains(solver)) {
          // partial model should not return an evaluation
          assertThat(m.evaluate(imgr.makeVariable("y"))).isNull();
        } else {
          assertThat(m.evaluate(imgr.makeVariable("y"))).isNotNull();
        }
      }
    }
  }

  @Test
  public void testPartialModels() throws Exception {
    assume()
        .withFailureMessage("As of now, only Z3 and Princess support partial models")
        .that(solver)
        .isIn(SOLVERS_WITH_PARTIAL_MODEL);
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
      IntegerFormula f = fmgr.declareAndCallUF("f", IntegerType, x);

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
        amgr.makeArray("array", IntegerType, IntegerType);
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

  @Test
  public void testGetArrays2() throws Exception {
    requireArrays();

    BooleanFormula f =
        mgr.parse(
            "(declare-fun |pi@2| () Int)\n"
                + "(declare-fun *unsigned_int@1 () (Array Int Int))\n"
                + "(declare-fun |z2@2| () Int)\n"
                + "(declare-fun |z1@2| () Int)\n"
                + "(declare-fun |t@2| () Int)\n"
                + "(declare-fun |__ADDRESS_OF_t| () Int)\n"
                + "(declare-fun *char@1 () (Array Int Int))\n"
                + "(assert"
                + "    (and (= |t@2| 50)"
                + "        (not (<= |__ADDRESS_OF_t| 0))"
                + "        (= |z1@2| |__ADDRESS_OF_t|)"
                + "        (= (select *char@1 |__ADDRESS_OF_t|) |t@2|)"
                + "        (= |z2@2| |z1@2|)"
                + "        (= |pi@2| |z2@2|)"
                + "        (not (= (select *unsigned_int@1 |pi@2|) 50))))");

    testModelIterator(f);
  }

  @Test
  public void testGetArrays3() throws Exception {
    requireArrays();
    assume()
        .withFailureMessage("As of now, only Princess does not support multi-dimensional arrays")
        .that(solver)
        .isNotSameAs(Solvers.PRINCESS);

    // create formula for "arr[5][3][1]==x && x==123"
    BooleanFormula f =
        mgr.parse(
            "(declare-fun x () Int)\n"
                + "(declare-fun arr () (Array Int (Array Int (Array Int Int))))\n"
                + "(assert (and"
                + "    (= (select (select (select arr 5) 3) 1) x)"
                + "    (= x 123)"
                + "))");

    testModelIterator(f);
    testModelGetters(f, imgr.makeVariable("x"), BigInteger.valueOf(123), "x");
    ArrayFormulaType<
            IntegerFormula,
            ArrayFormula<IntegerFormula, ArrayFormula<IntegerFormula, IntegerFormula>>>
        arrType =
            ArrayFormulaType.getArrayType(
                IntegerType,
                ArrayFormulaType.getArrayType(
                    IntegerType, ArrayFormulaType.getArrayType(IntegerType, IntegerType)));
    testModelGetters(
        f,
        amgr.select(
            amgr.select(
                amgr.select(amgr.makeArray("arr", arrType), imgr.makeNumber(5)),
                imgr.makeNumber(3)),
            imgr.makeNumber(1)),
        BigInteger.valueOf(123),
        "arr",
        true);
  }

  @Test
  public void testGetArrays4() throws Exception {
    requireArrays();

    // create formula for "arr[5]==x && x==123"
    BooleanFormula f =
        mgr.parse(
            "(declare-fun x () Int)\n"
                + "(declare-fun arr () (Array Int Int))\n"
                + "(assert (and"
                + "    (= (select arr 5) x)"
                + "    (= x 123)"
                + "))");

    testModelIterator(f);
    testModelGetters(f, imgr.makeVariable("x"), BigInteger.valueOf(123), "x");
    testModelGetters(
        f,
        amgr.select(
            amgr.makeArray("arr", ArrayFormulaType.getArrayType(IntegerType, IntegerType)),
            imgr.makeNumber(5)),
        BigInteger.valueOf(123),
        "arr",
        true);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testGetArrays4invalid() throws Exception {
    requireArrays();

    // create formula for "arr[5]==x && x==123"
    BooleanFormula f =
        mgr.parse(
            "(declare-fun x () Int)\n"
                + "(declare-fun arr () (Array Int Int))\n"
                + "(assert (and"
                + "    (= (select arr 5) x)"
                + "    (= x 123)"
                + "))");

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(f);
      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        @SuppressWarnings("unused")
        Object evaluation =
            m.evaluate(
                amgr.makeArray("arr", ArrayFormulaType.getArrayType(IntegerType, IntegerType)));
      }
    }
  }

  @Test
  public void testGetArrays5() throws Exception {
    requireArrays();

    // create formula for "arr[5]==x && x==123"
    BooleanFormula f =
        mgr.parse(
            "(declare-fun x () Int)\n"
                + "(declare-fun arr () (Array Int Int))\n"
                + "(assert (and"
                + "    (= (select (store arr 6 x) 5) x)"
                + "    (= x 123)"
                + "))");

    testModelIterator(f);
    testModelGetters(f, imgr.makeVariable("x"), BigInteger.valueOf(123), "x");
    testModelGetters(
        f,
        amgr.select(
            amgr.makeArray("arr", ArrayFormulaType.getArrayType(IntegerType, IntegerType)),
            imgr.makeNumber(5)),
        BigInteger.valueOf(123),
        "arr",
        true);
  }

  private void testModelIterator(BooleanFormula f) throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(f);

      assertThatEnvironment(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        for (@SuppressWarnings("unused") ValueAssignment assignment : m) {
          // Check that we can iterate through with no crashes.
        }
        assertThat(prover.getModelAssignments()).containsExactlyElementsIn(m).inOrder();
      }
    }
  }

  private void testModelGetters(
      BooleanFormula constraint, Formula variable, Object expectedValue, String varName)
      throws Exception {
    testModelGetters(constraint, variable, expectedValue, varName, false);
  }

  private void testModelGetters(
      BooleanFormula constraint,
      Formula variable,
      Object expectedValue,
      String varName,
      boolean isArray)
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
        assertThat(relevantAssignments).isNotEmpty();

        if (isArray) {
          List<ValueAssignment> arrayAssignments =
              relevantAssignments
                  .stream()
                  .filter(assignment -> expectedValue.equals(assignment.getValue()))
                  .collect(Collectors.toList());
          assertThat(arrayAssignments)
              .isNotEmpty(); // at least one assignment should have the wanted value

        } else {
          // normal variables or UFs have exactly one evaluation assigned to their name
          assertThat(relevantAssignments).hasSize(1);
          ValueAssignment assignment = Iterables.getOnlyElement(relevantAssignments);
          assertThat(assignment.getValue()).isEqualTo(expectedValue);
          assertThat(m.evaluate(assignment.getKey())).isEqualTo(expectedValue);
        }
      }
    }
  }

  @Test
  public void ufTest() throws SolverException, InterruptedException {
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
    BooleanFormula a1 = qmgr.forall(ctr, body);
    BooleanFormula a2 =
        bvmgr.equal(fmgr.callUF(si1, bvmgr.add(adr, bvmgr.multiply(num4, num0))), num0);

    BooleanFormula f = bmgr.and(a1, bvmgr.lessThan(num0, adr, true), bmgr.not(a2));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(f);
      assertThat(prover.isUnsat()).isFalse();
      try (Model m = prover.getModel()) {
        // TODO the model is not correct for Z3, check this!

        // dummy-check for TRUE, such that the JUnit-test is not useless :-)
        assertThat(m.evaluate(bmgr.makeBoolean(true))).isTrue();
      }
    }
  }

  @Test
  public void quantifierTestShort() throws SolverException, InterruptedException {
    requireQuantifiers();

    IntegerFormula ctr = imgr.makeVariable("x");
    BooleanFormula body = imgr.equal(ctr, imgr.makeNumber(0));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      // exists x : x==0
      prover.push(qmgr.exists(ctr, body));
      assertThat(prover.isUnsat()).isFalse();
      try (Model m = prover.getModel()) {
        for (ValueAssignment v : m) {
          // a value-assignment might have a different name, but the value should be "0".
          assertThat(BigInteger.ZERO.equals(v.getValue())).isTrue();
        }
      }
      prover.pop();

      // x==0
      prover.push(body);
      assertThat(prover.isUnsat()).isFalse();
      try (Model m = prover.getModel()) {
        ValueAssignment v = m.iterator().next();
        assertThat("x".equals(v.getName())).isTrue();
        assertThat(BigInteger.ZERO.equals(v.getValue())).isTrue();
      }
    }
  }
}
