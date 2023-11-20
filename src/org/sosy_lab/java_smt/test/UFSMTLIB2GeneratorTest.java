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

import java.util.ArrayList;
import java.util.Objects;
import org.junit.Assert;
import org.junit.Test;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class UFSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /**
   * Integer and Rationals not supported by BOOLECTOR Rationals not supported by PRINCESS Z3 runs
   * only when executed separately from other solvers
   */
  public void clearGenerator() {
    Generator.lines.delete(0, Generator.lines.length());
    Generator.registeredVariables.clear();
    Generator.executedAggregator.clear();
  }

  @Test
  public void testdeclareUFBoolean() {
    clearGenerator();
    FunctionDeclaration<BooleanFormula> a =
        fmgr.declareUF("a", FormulaType.BooleanType, FormulaType.BooleanType);
    FunctionDeclaration<BooleanFormula> b =
        fmgr.declareUF("b", FormulaType.BooleanType, new ArrayList<>());

    BooleanFormula c = fmgr.callUF(a, bmgr.makeFalse());
    BooleanFormula d = fmgr.callUF(b);

    BooleanFormula constraint = bmgr.equivalence(c, d);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Bool) Bool)\n"
            + "(declare-fun b () Bool)\n"
            + "(assert (= (a false) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFInteger() {
    requireIntegers();
    clearGenerator();
    FunctionDeclaration<IntegerFormula> a =
        fmgr.declareUF("a", FormulaType.IntegerType, FormulaType.IntegerType);
    FunctionDeclaration<IntegerFormula> b =
        fmgr.declareUF("b", FormulaType.IntegerType, new ArrayList<>());

    IntegerFormula c = fmgr.callUF(a, imgr.makeNumber(4));
    IntegerFormula d = fmgr.callUF(b);

    BooleanFormula constraint = imgr.equal(c, d);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Int) Int)\n" + "(declare-fun b () Int)\n" + "(assert (= (a 4) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFRational() {
    requireRationals();
    clearGenerator();
    FunctionDeclaration<RationalFormula> a =
        fmgr.declareUF("a", FormulaType.RationalType, FormulaType.RationalType);
    FunctionDeclaration<RationalFormula> b =
        fmgr.declareUF("b", FormulaType.RationalType, new ArrayList<>());

    RationalFormula c = fmgr.callUF(a, Objects.requireNonNull(rmgr).makeNumber(4));
    RationalFormula d = fmgr.callUF(b);

    BooleanFormula constraint = rmgr.equal(c, d);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Real) Real)\n" + "(declare-fun b () Real)\n" + "(assert (= (a 4) b))\n";

    String expectedResultSMTInterpol =
        "(declare-fun a (Real) Real)\n" + "(declare-fun b () Real)\n" + "(assert (= (a 4.0) b))\n";

    Assert.assertTrue(
        actualResult.equals(expectedResult) || actualResult.equals(expectedResultSMTInterpol));
  }

  @Test
  public void testDeclareUFBitvectors() {
    requireBitvectors();
    clearGenerator();
    FunctionDeclaration<BitvectorFormula> a =
        fmgr.declareUF(
            "a", FormulaType.getBitvectorTypeWithSize(4), FormulaType.getBitvectorTypeWithSize(4));
    FunctionDeclaration<BitvectorFormula> b =
        fmgr.declareUF("b", FormulaType.getBitvectorTypeWithSize(4), new ArrayList<>());

    BitvectorFormula c = fmgr.callUF(a, Objects.requireNonNull(bvmgr).makeBitvector(4, 2));
    BitvectorFormula d = fmgr.callUF(b);

    BooleanFormula constraint = bvmgr.equal(c, d);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(declare-fun b () (_ BitVec 4))\n"
            + "(assert (= (a #b0010) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFArrays() {
    requireArrays();
    requireIntegers();
    clearGenerator();
    FunctionDeclaration<ArrayFormula<IntegerFormula, IntegerFormula>> a =
        fmgr.declareUF(
            "a",
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            FormulaType.getArrayType(
                FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                FormulaType.IntegerType));
    FunctionDeclaration<ArrayFormula<IntegerFormula, IntegerFormula>> b =
        fmgr.declareUF(
            "b",
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            new ArrayList<>());
    FunctionDeclaration<BooleanFormula> constr =
        fmgr.declareUF(
            "constr",
            FormulaType.BooleanType,
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType));

    ArrayFormula<IntegerFormula, IntegerFormula> c =
        fmgr.callUF(
            a,
            Objects.requireNonNull(amgr)
                .makeArray(
                    "test",
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.IntegerType));
    ArrayFormula<IntegerFormula, IntegerFormula> d = fmgr.callUF(b);

    BooleanFormula constraint = fmgr.callUF(constr, c, d);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(declare-const test (Array (Array Int Int) Int))\n"
            + "(declare-fun b () (Array Int Int))\n"
            + "(assert (constr (a test) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBoolean() {
    clearGenerator();
    BooleanFormula a = fmgr.declareAndCallUF("a", FormulaType.BooleanType, bmgr.makeFalse());
    BooleanFormula b = fmgr.declareAndCallUF("b", FormulaType.BooleanType);

    BooleanFormula constraint = bmgr.equivalence(a, b);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Bool) Bool)\n"
            + "(declare-fun b () Bool)\n"
            + "(assert (= (a false) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFInteger() {
    requireIntegers();
    clearGenerator();
    IntegerFormula a = fmgr.declareAndCallUF("a", FormulaType.IntegerType, imgr.makeNumber(4));
    IntegerFormula b = fmgr.declareAndCallUF("b", FormulaType.IntegerType);

    BooleanFormula constraint = imgr.equal(a, b);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Int) Int)\n" + "(declare-fun b () Int)\n" + "(assert (= (a 4) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFRational() {
    requireRationals();
    clearGenerator();
    RationalFormula a =
        fmgr.declareAndCallUF(
            "a", FormulaType.RationalType, Objects.requireNonNull(rmgr).makeNumber(4));
    RationalFormula b = fmgr.declareAndCallUF("b", FormulaType.RationalType);

    BooleanFormula constraint = rmgr.equal(a, b);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Real) Real)\n" + "(declare-fun b () Real)\n" + "(assert (= (a 4) b))\n";

    String expectedResultSMTInterpol =
        "(declare-fun a (Real) Real)\n" + "(declare-fun b () Real)\n" + "(assert (= (a 4.0) b))\n";

    Assert.assertTrue(
        actualResult.equals(expectedResult) || actualResult.equals(expectedResultSMTInterpol));
  }

  @Test
  public void testDeclareAndCallUFBitvectors() {
    requireBitvectors();
    clearGenerator();
    BitvectorFormula a =
        fmgr.declareAndCallUF(
            "a",
            FormulaType.getBitvectorTypeWithSize(4),
            Objects.requireNonNull(bvmgr).makeBitvector(4, 2));
    BitvectorFormula b =
        fmgr.declareAndCallUF("b", FormulaType.getBitvectorTypeWithSize(4), new ArrayList<>());

    BooleanFormula constraint = bvmgr.equal(a, b);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(declare-fun b () (_ BitVec 4))\n"
            + "(assert (= (a #b0010) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFArrays() {
    requireArrays();
    requireIntegers();
    clearGenerator();
    ArrayFormula<IntegerFormula, IntegerFormula> a =
        fmgr.declareAndCallUF(
            "a",
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            Objects.requireNonNull(amgr)
                .makeArray(
                    "test",
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.IntegerType));
    ArrayFormula<IntegerFormula, IntegerFormula> b =
        fmgr.declareAndCallUF(
            "b", FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType));

    BooleanFormula constraint = fmgr.declareAndCallUF("constr", FormulaType.BooleanType, a, b);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(declare-const test (Array (Array Int Int) Int))\n"
            + "(declare-fun b () (Array Int Int))\n"
            + "(assert (constr (a test) b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
}
