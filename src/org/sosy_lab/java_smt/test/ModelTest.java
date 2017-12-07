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
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** Test that values from models are appropriately parsed. */
@RunWith(Parameterized.class)
public class ModelTest extends SolverBasedTest0 {

  private static final ImmutableList<Solvers> SOLVERS_WITH_PARTIAL_MODEL =
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
  public void testGetSmallIntegers() throws SolverException, InterruptedException {
    testModelGetters(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(10)),
        imgr.makeVariable("x"),
        BigInteger.valueOf(10),
        "x");
  }

  @Test
  public void testGetNegativeIntegers() throws SolverException, InterruptedException {
    testModelGetters(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(-10)),
        imgr.makeVariable("x"),
        BigInteger.valueOf(-10),
        "x");
  }

  @Test
  public void testGetLargeIntegers() throws SolverException, InterruptedException {
    BigInteger large = new BigInteger("1000000000000000000000000000000000000000");
    testModelGetters(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(large)),
        imgr.makeVariable("x"),
        large,
        "x");
  }

  @Test
  public void testGetSmallIntegralRationals() throws SolverException, InterruptedException {
    requireRationals();
    assert rmgr != null;
    testModelGetters(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.makeVariable("x"),
        Rational.ONE,
        "x");
  }

  @Test
  public void testGetLargeIntegralRationals() throws SolverException, InterruptedException {
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
  public void testGetRationals() throws SolverException, InterruptedException {
    requireRationals();
    assert rmgr != null;
    testModelGetters(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("1/3"))),
        rmgr.makeVariable("x"),
        Rational.ofString("1/3"),
        "x");
  }

  @Test
  public void testGetBooleans() throws SolverException, InterruptedException {
    testModelGetters(bmgr.makeVariable("x"), bmgr.makeBoolean(true), true, "x");
  }

  @Test
  public void testGetUFs() throws SolverException, InterruptedException {
    IntegerFormula x =
        fmgr.declareAndCallUF("UF", IntegerType, ImmutableList.of(imgr.makeVariable("arg")));
    testModelGetters(imgr.equal(x, imgr.makeNumber(1)), x, BigInteger.ONE, "UF");
  }

  @Test
  public void testGetMultipleUFs() throws SolverException, InterruptedException {
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

      assertThat(prover).isSatisfiable();

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
  public void testQuantifiedUF() throws SolverException, InterruptedException {
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
      assertThat(prover).isSatisfiable();

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
  public void testGetBitvectors() throws SolverException, InterruptedException {
    requireBitvectors();
    assert bvmgr != null;

    testModelGetters(
        bvmgr.equal(bvmgr.makeVariable(1, "x"), bvmgr.makeBitvector(1, BigInteger.ONE)),
        bvmgr.makeVariable(1, "x"),
        BigInteger.ONE,
        "x");
  }

  @Test
  public void testGetModelAssignments() throws SolverException, InterruptedException {
    testModelIterator(
        bmgr.and(
            imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(1)),
            imgr.equal(imgr.makeVariable("x"), imgr.makeVariable("y"))));
  }

  @Test
  public void testEmptyStackModel() throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      assertThat(prover).isSatisfiable();
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
  public void testNonExistantSymbol() throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.makeBoolean(true));
      assertThat(prover).isSatisfiable();

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
  public void testPartialModels() throws SolverException, InterruptedException {
    assume()
        .withMessage("As of now, only Z3 and Princess support partial models")
        .that(solver)
        .isIn(SOLVERS_WITH_PARTIAL_MODEL);
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      IntegerFormula x = imgr.makeVariable("x");
      prover.push(imgr.equal(x, x));
      assertThat(prover).isSatisfiable();
      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(x)).isEqualTo(null);
        assertThat(m).isEmpty();
      }
    }
  }

  @Test
  public void testPartialModelsUF() throws SolverException, InterruptedException {
    assume()
        .withMessage("As of now, only Z3 and Princess support partial model evaluation")
        .that(solver)
        .isIn(ImmutableList.of(Solvers.Z3, Solvers.PRINCESS));
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula f = fmgr.declareAndCallUF("f", IntegerType, x);

      prover.push(imgr.equal(x, imgr.makeNumber(1)));
      assertThat(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        assertThat(m.evaluate(f)).isEqualTo(null);
      }
    }
  }

  @Test
  public void testEvaluatingConstants() throws SolverException, InterruptedException {
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
  public void testGetArrays() throws SolverException, InterruptedException {
    requireArrays();
    assert amgr != null;

    ArrayFormula<IntegerFormula, IntegerFormula> array =
        amgr.makeArray("array", IntegerType, IntegerType);
    ArrayFormula<IntegerFormula, IntegerFormula> updated =
        amgr.store(array, imgr.makeNumber(1), imgr.makeNumber(1));

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(amgr.select(updated, imgr.makeNumber(1)), imgr.makeNumber(1)));

      assertThat(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        for (@SuppressWarnings("unused") ValueAssignment assignment : m) {
          // Check that we can iterate through with no crashes.
        }
        assertThat(m.evaluate(amgr.select(updated, imgr.makeNumber(1)))).isEqualTo(BigInteger.ONE);
      }
    }
  }

  @Test
  public void testGetArrays2() throws SolverException, InterruptedException {
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
  public void testGetArrays3() throws SolverException, InterruptedException {
    requireArrays();
    assume()
        .withMessage("As of now, only Princess does not support multi-dimensional arrays")
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
  public void testGetArrays4() throws SolverException, InterruptedException {
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
  public void testGetArrays4invalid() throws SolverException, InterruptedException {
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
      assertThat(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        @SuppressWarnings("unused")
        Object evaluation =
            m.evaluate(
                amgr.makeArray("arr", ArrayFormulaType.getArrayType(IntegerType, IntegerType)));
      }
    }
  }

  @Test
  public void testGetArrays5() throws SolverException, InterruptedException {
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

      assertThat(prover).isSatisfiable();

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
      throws SolverException, InterruptedException {
    testModelGetters(constraint, variable, expectedValue, varName, false);
  }

  private void testModelGetters(
      BooleanFormula constraint,
      Formula variable,
      Object expectedValue,
      String varName,
      boolean isArray)
      throws SolverException, InterruptedException {

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(constraint);
      assertThat(prover).isSatisfiable();

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

    checkModelIteration(f, true);
    checkModelIteration(f, false);
  }

  private void checkModelIteration(BooleanFormula f, boolean useOptProver)
      throws SolverException, InterruptedException {
    try (BasicProverEnvironment<?> prover =
        useOptProver
            ? context.newOptimizationProverEnvironment()
            : context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(f);
      assertThat(prover.isUnsat()).isFalse();
      try (Model m = prover.getModel()) {
        for (@SuppressWarnings("unused") ValueAssignment assignment : m) {
          // Check that we can iterate through with no crashes.
        }
        assertThat(prover.getModelAssignments()).containsExactlyElementsIn(m).inOrder();
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

  static final String SMALL_ARRAY_QUERY =
      "(declare-fun A1 () (Array Int Int))"
          + "(declare-fun A2 () (Array Int Int))"
          + "(declare-fun X () Int)"
          + "(declare-fun Y () Int)"
          + "(assert (= A1 (store A2 X Y)))";

  static final String BIG_ARRAY_QUERY =
      "(declare-fun |V#2@| () Int)"
          + "(declare-fun z3name!115 () Int)"
          + "(declare-fun P42 () Bool)"
          + "(declare-fun M@3 () Int)"
          + "(declare-fun P43 () Bool)"
          + "(declare-fun |V#1@| () Int)"
          + "(declare-fun z3name!114 () Int)"
          + "(declare-fun P44 () Bool)"
          + "(declare-fun M@2 () Int)"
          + "(declare-fun P45 () Bool)"
          + "(declare-fun |It15@5| () Int)"
          + "(declare-fun |It13@5| () Int)"
          + "(declare-fun |H@12| () (Array Int Int))"
          + "(declare-fun |H@13| () (Array Int Int))"
          + "(declare-fun |It14@5| () Int)"
          + "(declare-fun |IN@5| () Int)"
          + "(declare-fun |It12@5| () Int)"
          + "(declare-fun |It11@5| () Int)"
          + "(declare-fun |It9@5| () Int)"
          + "(declare-fun |H@11| () (Array Int Int))"
          + "(declare-fun |It10@5| () Int)"
          + "(declare-fun |It8@5| () Int)"
          + "(declare-fun |Anew@3| () Int)"
          + "(declare-fun |Aprev@3| () Int)"
          + "(declare-fun |H@10| () (Array Int Int))"
          + "(declare-fun |At7@5| () Int)"
          + "(declare-fun |H@9| () (Array Int Int))"
          + "(declare-fun |At6@5| () Int)"
          + "(declare-fun |Anext@3| () Int)"
          + "(declare-fun |H@8| () (Array Int Int))"
          + "(declare-fun |At5@5| () Int)"
          + "(declare-fun |H@7| () (Array Int Int))"
          + "(declare-fun |At4@5| () Int)"
          + "(declare-fun |at3@5| () Int)"
          + "(declare-fun |ahead@3| () Int)"
          + "(declare-fun |anew@3| () Int)"
          + "(declare-fun gl@ () Int)"
          + "(declare-fun |It7@5| () Int)"
          + "(declare-fun |It6@5| () Int)"
          + "(declare-fun |It5@5| () Int)"
          + "(declare-fun |Ivalue@3| () Int)"
          + "(declare-fun i@2 () (Array Int Int))"
          + "(declare-fun i@3 () (Array Int Int))"
          + "(declare-fun P46 () Bool)"
          + "(declare-fun |It4@5| () Int)"
          + "(declare-fun |It4@3| () Int)"
          + "(declare-fun |IT@5| () Int)"
          + "(declare-fun |gl_read::T@4| () Int)"
          + "(declare-fun __VERIFIER_nondet_int@4 () Int)"
          + "(declare-fun |It15@3| () Int)"
          + "(declare-fun |It13@3| () Int)"
          + "(declare-fun |H@6| () (Array Int Int))"
          + "(declare-fun |It14@3| () Int)"
          + "(declare-fun |IN@3| () Int)"
          + "(declare-fun |It12@3| () Int)"
          + "(declare-fun |It11@3| () Int)"
          + "(declare-fun |It9@3| () Int)"
          + "(declare-fun |H@5| () (Array Int Int))"
          + "(declare-fun |It10@3| () Int)"
          + "(declare-fun |It8@3| () Int)"
          + "(declare-fun |Anew@2| () Int)"
          + "(declare-fun |Aprev@2| () Int)"
          + "(declare-fun |H@4| () (Array Int Int))"
          + "(declare-fun |At7@3| () Int)"
          + "(declare-fun |H@3| () (Array Int Int))"
          + "(declare-fun |At6@3| () Int)"
          + "(declare-fun |Anext@2| () Int)"
          + "(declare-fun |H@2| () (Array Int Int))"
          + "(declare-fun |At5@3| () Int)"
          + "(declare-fun |H@1| () (Array Int Int))"
          + "(declare-fun |At4@3| () Int)"
          + "(declare-fun |at3@3| () Int)"
          + "(declare-fun |ahead@2| () Int)"
          + "(declare-fun |anew@2| () Int)"
          + "(declare-fun |It7@3| () Int)"
          + "(declare-fun |It6@3| () Int)"
          + "(declare-fun |It5@3| () Int)"
          + "(declare-fun |Ivalue@2| () Int)"
          + "(declare-fun i@1 () (Array Int Int))"
          + "(declare-fun P47 () Bool)"
          + "(declare-fun |IT@3| () Int)"
          + "(declare-fun |gl_read::T@3| () Int)"
          + "(declare-fun __VERIFIER_nondet_int@2 () Int)"
          + "(assert "
          + "  (and (not (<= gl@ 0))"
          + "       (not (<= gl@ (- 64)))"
          + "       (= |gl_read::T@3| __VERIFIER_nondet_int@2)"
          + "       (= |Ivalue@2| |gl_read::T@3|)"
          + "       (= |It4@3| 20)"
          + "       (= |IT@3| z3name!114)"
          + "       (not (<= |V#1@| 0))"
          + "       (= |IN@3| |IT@3|)"
          + "       (not (<= |V#1@| (+ 64 gl@)))"
          + "       (not (<= |V#1@| (- 160)))"
          + "       (not (<= (+ |V#1@| (* 8 |It4@3|)) 0))"
          + "       (or (and P47 (not (<= |IN@3| 0))) (and (not P47) (not (>= |IN@3| 0))))"
          + "       (= i@2 (store i@1 |IN@3| |Ivalue@2|))"
          + "       (= |It5@3| |IN@3|)"
          + "       (= |It6@3| (+ 4 |It5@3|))"
          + "       (= |It7@3| |It6@3|)"
          + "       (= |anew@2| |It7@3|)"
          + "       (= |ahead@2| gl@)"
          + "       (= |at3@3| (select |H@1| |ahead@2|))"
          + "       (= |Anew@2| |anew@2|)"
          + "       (= |Aprev@2| |ahead@2|)"
          + "       (= |Anext@2| |at3@3|)"
          + "       (= |At4@3| |Anext@2|)"
          + "       (= |At5@3| (+ 4 |At4@3|))"
          + "       (= |H@2| (store |H@1| |At5@3| |Anew@2|))"
          + "       (= |H@3| (store |H@2| |Anew@2| |Anext@2|))"
          + "       (= |At6@3| |Anew@2|)"
          + "       (= |At7@3| (+ 4 |At6@3|))"
          + "       (= |H@4| (store |H@3| |At7@3| |Aprev@2|))"
          + "       (= |H@5| (store |H@4| |Aprev@2| |Anew@2|))"
          + "       (= |It8@3| |IN@3|)"
          + "       (= |It9@3| (+ 12 |It8@3|))"
          + "       (= |It10@3| |IN@3|)"
          + "       (= |It11@3| (+ 12 |It10@3|))"
          + "       (= |H@6| (store |H@5| |It9@3| |It11@3|))"
          + "       (= |It12@3| |IN@3|)"
          + "       (= |It13@3| (+ 12 |It12@3|))"
          + "       (= |It14@3| |IN@3|)"
          + "       (= |It15@3| (+ 12 |It14@3|))"
          + "       (= |H@7| (store |H@6| |It13@3| |It15@3|))"
          + "       (= |gl_read::T@4| __VERIFIER_nondet_int@4)"
          + "       (= |Ivalue@3| |gl_read::T@4|)"
          + "       (= |It4@5| 20)"
          + "       (= |IT@5| z3name!115)"
          + "       (not (<= |V#2@| 0))"
          + "       (= |IN@5| |IT@5|)"
          + "       (not (<= |V#2@| (+ |V#1@| (* 8 |It4@3|))))"
          + "       (not (<= |V#2@| (+ 160 |V#1@|)))"
          + "       (not (<= |V#2@| (- 160)))"
          + "       (not (<= (+ |V#2@| (* 8 |It4@5|)) 0))"
          + "       (or (and P46 (not (<= |IN@5| 0))) (and (not P46) (not (>= |IN@5| 0))))"
          + "       (= i@3 (store i@2 |IN@5| |Ivalue@3|))"
          + "       (= |It5@5| |IN@5|)"
          + "       (= |It6@5| (+ 4 |It5@5|))"
          + "       (= |It7@5| |It6@5|)"
          + "       (= |anew@3| |It7@5|)"
          + "       (= |ahead@3| gl@)"
          + "       (= |at3@5| (select |H@7| |ahead@3|))"
          + "       (= |Anew@3| |anew@3|)"
          + "       (= |Aprev@3| |ahead@3|)"
          + "       (= |Anext@3| |at3@5|)"
          + "       (= |At4@5| |Anext@3|)"
          + "       (= |At5@5| (+ 4 |At4@5|))"
          + "       (= |H@8| (store |H@7| |At5@5| |Anew@3|))"
          + "       (= |H@9| (store |H@8| |Anew@3| |Anext@3|))"
          + "       (= |At6@5| |Anew@3|)"
          + "       (= |At7@5| (+ 4 |At6@5|))"
          + "       (= |H@10| (store |H@9| |At7@5| |Aprev@3|))"
          + "       (= |H@11| (store |H@10| |Aprev@3| |Anew@3|))"
          + "       (= |It8@5| |IN@5|)"
          + "       (= |It9@5| (+ 12 |It8@5|))"
          + "       (= |It10@5| |IN@5|)"
          + "       (= |It11@5| (+ 12 |It10@5|))"
          + "       (= |H@12| (store |H@11| |It9@5| |It11@5|))"
          + "       (= |It12@5| |IN@5|)"
          + "       (= |It13@5| (+ 12 |It12@5|))"
          + "       (= |It14@5| |IN@5|)"
          + "       (= |It15@5| (+ 12 |It14@5|))"
          + "       (= |H@13| (store |H@12| |It13@5| |It15@5|))"
          + "       (or (and P45 (not (= M@2 0)))  (and (not P45) (= z3name!114 0)))"
          + "       (or (and P44 (= M@2 0)) (and (not P44) (= z3name!114 |V#1@|)))"
          + "       (or (and P43 (not (= M@3 0))) (and (not P43) (= z3name!115 0)))"
          + "       (or (and P42 (= M@3 0)) (and (not P42) (= z3name!115 |V#2@|)))))";

  static final String SMALL_BV_FLOAT_QUERY =
      "(declare-fun |f@2| () (_ FloatingPoint 8 23))"
          + "(declare-fun |p@3| () (_ BitVec 32))"
          + "(declare-fun *float@1 () (Array (_ BitVec 32) (_ FloatingPoint 8 23)))"
          + "(declare-fun |i@3| () (_ BitVec 32))"
          + "(declare-fun |Ai@| () (_ BitVec 32))"
          + "(declare-fun *unsigned_int@1 () (Array (_ BitVec 32) (_ BitVec 32)))"
          + "(assert (and (bvslt #x00000000 |Ai@|)"
          + "     (bvslt #x00000000 (bvadd |Ai@| #x00000020))"
          + "     (= |i@3| #x00000000)"
          + "     (= |p@3| |Ai@|)"
          + "     (= (select *unsigned_int@1 |Ai@|) |i@3|)"
          + "     (= |f@2| (select *float@1 |p@3|))"
          + "     (not (fp.eq ((_ to_fp 11 52) roundNearestTiesToEven |f@2|)"
          + "                 (_ +zero 11 52)))))";

  static final String SMALL_BV_FLOAT_QUERY2 =
      "(declare-fun a () (_ FloatingPoint 8 23))"
          + "(declare-fun A () (Array (_ BitVec 32) (_ FloatingPoint 8 23)))"
          + "(assert (= a (select A #x00000000)))";

  @Test
  public void arrayTest() throws SolverException, InterruptedException {
    requireArrays();
    requireOptimization();
    requireFloats();
    requireBitvectors();
    // only Z3 fulfills these requirements

    for (String query :
        Lists.newArrayList(
            SMALL_ARRAY_QUERY, BIG_ARRAY_QUERY, SMALL_BV_FLOAT_QUERY, SMALL_BV_FLOAT_QUERY2)) {
      BooleanFormula formula = context.getFormulaManager().parse(query);
      checkModelIteration(formula, true);
      checkModelIteration(formula, false);
    }
  }
}
