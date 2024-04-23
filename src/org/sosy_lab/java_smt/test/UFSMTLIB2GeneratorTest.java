// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import java.util.ArrayList;
import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.basicimpl.GeneratorException;

public class UFSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /**
   * Integer and Rationals not supported by BOOLECTOR Rationals not supported by PRINCESS Z3 runs
   * only when executed separately from other solvers
   */
  public void clearGenerator() {
    Generator.setIsLoggingEnabled(true);
    Generator.lines.delete(0, Generator.lines.length());
    Generator.registeredVariables.clear();
    Generator.executedAggregator.clear();
  }

  @Test
  public void testdeclareUFBooleanWithInput() {
    clearGenerator();
    requireBooleanUFs();
    FunctionDeclaration<BooleanFormula> a =
        fmgr.declareUF("a", FormulaType.BooleanType, FormulaType.BooleanType);
    FunctionDeclaration<BooleanFormula> b =
        fmgr.declareUF("b", FormulaType.BooleanType, FormulaType.BooleanType);

    BooleanFormula c = fmgr.callUF(a, bmgr.makeFalse());
    BooleanFormula d = fmgr.callUF(b, bmgr.makeTrue());

    BooleanFormula constraint = bmgr.equivalence(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Bool) Bool)\n"
            + "(declare-fun b (Bool) Bool)\n"
            + "(assert (= (a false) (b true)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testdeclareUFBooleanEmptyInput() {
    clearGenerator();
    requireBooleanUFs();
    requireNoArgumentsInUFs();
    FunctionDeclaration<BooleanFormula> a = fmgr.declareUF("a", FormulaType.BooleanType);
    FunctionDeclaration<BooleanFormula> b = fmgr.declareUF("b", FormulaType.BooleanType);

    BooleanFormula c = fmgr.callUF(a);
    BooleanFormula d = fmgr.callUF(b);

    BooleanFormula constraint = bmgr.equivalence(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () Bool)\n" + "(declare-fun b () Bool)\n" + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test(expected = GeneratorException.class)
  public void testdeclareUFInputException() {
    clearGenerator();
    requireBooleanUFs();
    requireStrings();
    FunctionDeclaration<BooleanFormula> a =
        fmgr.declareUF("a", FormulaType.BooleanType, FormulaType.StringType);
    FunctionDeclaration<BooleanFormula> b =
        fmgr.declareUF("b", FormulaType.BooleanType, new ArrayList<>());

    BooleanFormula c = fmgr.callUF(a, Objects.requireNonNull(smgr).makeString("test"));
    BooleanFormula d = fmgr.callUF(b);

    BooleanFormula constraint = bmgr.equivalence(c, d);

    Generator.assembleConstraint(constraint);
  }

  @Test(expected = GeneratorException.class)
  public void testdeclareUFOutputException() {
    clearGenerator();
    requireBooleanUFs();
    requireStrings();
    FunctionDeclaration<StringFormula> a =
        fmgr.declareUF("a", FormulaType.StringType, FormulaType.BooleanType);
    FunctionDeclaration<StringFormula> b =
        fmgr.declareUF("b", FormulaType.StringType, new ArrayList<>());

    StringFormula c = fmgr.callUF(a, bmgr.makeTrue());
    StringFormula d = fmgr.callUF(b);

    BooleanFormula constraint = Objects.requireNonNull(smgr).equal(c, d);

    Generator.assembleConstraint(constraint);
  }

  @Test
  public void testDeclareUFIntegerWithInput() {
    requireIntegers();
    clearGenerator();
    FunctionDeclaration<IntegerFormula> a =
        fmgr.declareUF("a", FormulaType.IntegerType, FormulaType.IntegerType);
    FunctionDeclaration<IntegerFormula> b =
        fmgr.declareUF("b", FormulaType.IntegerType, FormulaType.IntegerType);

    IntegerFormula c = fmgr.callUF(a, imgr.makeNumber(4));
    IntegerFormula d = fmgr.callUF(b, imgr.makeNumber(9));

    BooleanFormula constraint = imgr.equal(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Int) Int)\n"
            + "(declare-fun b (Int) Int)\n"
            + "(assert (= (a 4) (b 9)))"
            + "\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFIntegerWithoutInput() {
    requireIntegers();
    clearGenerator();
    requireNoArgumentsInUFs();
    FunctionDeclaration<IntegerFormula> a = fmgr.declareUF("a", FormulaType.IntegerType);
    FunctionDeclaration<IntegerFormula> b = fmgr.declareUF("b", FormulaType.IntegerType);

    IntegerFormula c = fmgr.callUF(a);
    IntegerFormula d = fmgr.callUF(b);

    BooleanFormula constraint = imgr.equal(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () Int)\n" + "(declare-fun b () Int)\n" + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFRationalWithInput() {
    requireRationals();
    clearGenerator();
    FunctionDeclaration<RationalFormula> a =
        fmgr.declareUF("a", FormulaType.RationalType, FormulaType.RationalType);
    FunctionDeclaration<RationalFormula> b =
        fmgr.declareUF("b", FormulaType.RationalType, FormulaType.RationalType);

    RationalFormula c = fmgr.callUF(a, Objects.requireNonNull(rmgr).makeNumber(4));
    RationalFormula d = fmgr.callUF(b, Objects.requireNonNull(rmgr).makeNumber(9));

    BooleanFormula constraint = rmgr.equal(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Real) Real)\n"
            + "(declare-fun b (Real) Real)\n"
            + "(assert (= (a 4) (b "
            + "9)))"
            + "\n";

    String expectedResultSMTInterpol =
        "(declare-fun a (Real) Real)\n"
            + "(declare-fun b (Real) Real)\n"
            + "(assert (= (a 4.0) "
            + "(b 9.0)))\n";

    assertThat(
            actualResult.equals(expectedResult) || actualResult.equals(expectedResultSMTInterpol))
        .isTrue();
  }

  @Test
  public void testDeclareUFRationalEmptyInput() {
    requireRationals();
    clearGenerator();
    requireNoArgumentsInUFs();
    FunctionDeclaration<RationalFormula> a = fmgr.declareUF("a", FormulaType.RationalType);
    FunctionDeclaration<RationalFormula> b = fmgr.declareUF("b", FormulaType.RationalType);

    RationalFormula c = fmgr.callUF(a);
    RationalFormula d = fmgr.callUF(b);

    BooleanFormula constraint = Objects.requireNonNull(rmgr).equal(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () Real)\n" + "(declare-fun b () Real)\n" + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFBitvectorsWithInput() {
    requireBitvectors();
    clearGenerator();
    FunctionDeclaration<BitvectorFormula> a =
        fmgr.declareUF(
            "a", FormulaType.getBitvectorTypeWithSize(4), FormulaType.getBitvectorTypeWithSize(4));
    FunctionDeclaration<BitvectorFormula> b =
        fmgr.declareUF(
            "b", FormulaType.getBitvectorTypeWithSize(4), FormulaType.getBitvectorTypeWithSize(4));

    BitvectorFormula c = fmgr.callUF(a, Objects.requireNonNull(bvmgr).makeBitvector(4, 2));
    BitvectorFormula d = fmgr.callUF(b, Objects.requireNonNull(bvmgr).makeBitvector(4, 3));

    BooleanFormula constraint = bvmgr.equal(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(declare-fun b ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(assert (= (a #b0010) (b #b0011)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFBitvectorsEmptyInput() {
    requireBitvectors();
    clearGenerator();
    requireNoArgumentsInUFs();
    FunctionDeclaration<BitvectorFormula> a =
        fmgr.declareUF("a", FormulaType.getBitvectorTypeWithSize(4));
    FunctionDeclaration<BitvectorFormula> b =
        fmgr.declareUF("b", FormulaType.getBitvectorTypeWithSize(4));

    BitvectorFormula c = fmgr.callUF(a);
    BitvectorFormula d = fmgr.callUF(b);

    BooleanFormula constraint = Objects.requireNonNull(bvmgr).equal(c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () (_ BitVec 4))\n"
            + "(declare-fun b () (_ BitVec 4))\n"
            + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFArraysWithInput() {
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
            FormulaType.getArrayType(
                FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                FormulaType.IntegerType));
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
    ArrayFormula<IntegerFormula, IntegerFormula> d =
        fmgr.callUF(
            b,
            Objects.requireNonNull(amgr)
                .makeArray(
                    "test",
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.IntegerType));

    BooleanFormula constraint = fmgr.callUF(constr, c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(declare-const test (Array (Array Int Int) Int))\n"
            + "(declare-fun b ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(assert (constr (a test) (b test)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFArraysEmptyInput() {
    requireArrays();
    requireIntegers();
    requireNoArgumentsInUFs();
    clearGenerator();
    FunctionDeclaration<ArrayFormula<IntegerFormula, IntegerFormula>> a =
        fmgr.declareUF(
            "a", FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType));
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

    ArrayFormula<IntegerFormula, IntegerFormula> c = fmgr.callUF(a);
    ArrayFormula<IntegerFormula, IntegerFormula> d = fmgr.callUF(b);

    BooleanFormula constraint = fmgr.callUF(constr, c, d);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a () (Array Int Int))\n"
            + "(declare-fun b () (Array Int Int))\n"
            + "(assert (constr a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBooleanWithInput() {
    clearGenerator();
    requireBooleanUFs();
    BooleanFormula a = fmgr.declareAndCallUF("a", FormulaType.BooleanType, bmgr.makeFalse());
    BooleanFormula b = fmgr.declareAndCallUF("b", FormulaType.BooleanType, bmgr.makeTrue());

    BooleanFormula constraint = bmgr.equivalence(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Bool) Bool)\n"
            + "(declare-fun b (Bool) Bool)\n"
            + "(assert (= (a false) (b true)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBooleanEmptyInput() {
    clearGenerator();
    requireBooleanUFs();
    requireNoArgumentsInUFs();
    BooleanFormula a = fmgr.declareAndCallUF("a", FormulaType.BooleanType);
    BooleanFormula b = fmgr.declareAndCallUF("b", FormulaType.BooleanType);

    BooleanFormula constraint = bmgr.equivalence(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () Bool)\n" + "(declare-fun b () Bool)\n" + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFIntegerWithInput() {
    requireIntegers();
    clearGenerator();
    IntegerFormula a = fmgr.declareAndCallUF("a", FormulaType.IntegerType, imgr.makeNumber(4));
    IntegerFormula b = fmgr.declareAndCallUF("b", FormulaType.IntegerType, imgr.makeNumber(9));

    BooleanFormula constraint = imgr.equal(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Int) Int)\n"
            + "(declare-fun b (Int) Int)\n"
            + "(assert (= (a 4) (b 9)))"
            + "\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFIntegerEmptyInput() {
    requireIntegers();
    requireNoArgumentsInUFs();
    clearGenerator();
    IntegerFormula a = fmgr.declareAndCallUF("a", FormulaType.IntegerType);
    IntegerFormula b = fmgr.declareAndCallUF("b", FormulaType.IntegerType);

    BooleanFormula constraint = imgr.equal(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () Int)\n" + "(declare-fun b () Int)\n" + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFRationalWithInput() {
    requireRationals();
    clearGenerator();
    RationalFormula a =
        fmgr.declareAndCallUF(
            "a", FormulaType.RationalType, Objects.requireNonNull(rmgr).makeNumber(4));
    RationalFormula b = fmgr.declareAndCallUF("b", FormulaType.RationalType, rmgr.makeNumber(9));

    BooleanFormula constraint = rmgr.equal(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a (Real) Real)\n"
            + "(declare-fun b (Real) Real)\n"
            + "(assert (= (a 4) (b "
            + "9)))\n";

    String expectedResultSMTInterpol =
        "(declare-fun a (Real) Real)\n"
            + "(declare-fun b (Real) Real)\n"
            + "(assert (= (a 4.0) "
            + "(b 9.0)))\n";

    assertThat(
            expectedResult.equals(actualResult) || actualResult.equals(expectedResultSMTInterpol))
        .isTrue();
  }

  @Test
  public void testDeclareAndCallUFRationalEmptyInput() {
    requireRationals();
    requireNoArgumentsInUFs();
    clearGenerator();
    RationalFormula a = fmgr.declareAndCallUF("a", FormulaType.RationalType);
    RationalFormula b = fmgr.declareAndCallUF("b", FormulaType.RationalType);

    BooleanFormula constraint = Objects.requireNonNull(rmgr).equal(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () Real)\n" + "(declare-fun b () Real)\n" + "(assert (= a b))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBitvectorsWithInput() {
    requireBitvectors();
    clearGenerator();
    BitvectorFormula a =
        fmgr.declareAndCallUF(
            "a",
            FormulaType.getBitvectorTypeWithSize(4),
            Objects.requireNonNull(bvmgr).makeBitvector(4, 2));
    BitvectorFormula b =
        fmgr.declareAndCallUF(
            "b", FormulaType.getBitvectorTypeWithSize(4), bvmgr.makeBitvector(4, 2));

    BooleanFormula constraint = bvmgr.equal(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(declare-fun b ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(assert (= (a #b0010) (b #b0010)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBitvectorsEmptyInput() {
    requireBitvectors();
    requireNoArgumentsInUFs();
    clearGenerator();
    BitvectorFormula a = fmgr.declareAndCallUF("a", FormulaType.getBitvectorTypeWithSize(4));
    BitvectorFormula b = fmgr.declareAndCallUF("b", FormulaType.getBitvectorTypeWithSize(4));

    BooleanFormula constraint = Objects.requireNonNull(bvmgr).equal(a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun a () (_ BitVec 4))\n"
            + "(declare-fun b () (_ BitVec 4))\n"
            + "(assert (= a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFArraysWithInput() {
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
            "b",
            FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            amgr.makeArray(
                "test",
                FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                FormulaType.IntegerType));

    BooleanFormula constraint = fmgr.declareAndCallUF("constr", FormulaType.BooleanType, a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(declare-const test (Array (Array Int Int) Int))\n"
            + "(declare-fun b ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(assert (constr (a test) (b test)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFArraysEmptyInput() {
    requireArrays();
    requireIntegers();
    requireNoArgumentsInUFs();
    clearGenerator();
    ArrayFormula<IntegerFormula, IntegerFormula> a =
        fmgr.declareAndCallUF(
            "a", FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType));
    ArrayFormula<IntegerFormula, IntegerFormula> b =
        fmgr.declareAndCallUF(
            "b", FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType));

    BooleanFormula constraint = fmgr.declareAndCallUF("constr", FormulaType.BooleanType, a, b);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a () (Array Int Int))\n"
            + "(declare-fun b () (Array Int Int))\n"
            + "(assert (constr a b))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
}
