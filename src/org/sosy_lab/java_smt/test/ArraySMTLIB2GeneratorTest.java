// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.basicimpl.GeneratorException;

public class ArraySMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Test(expected = GeneratorException.class)
  public void testdeclareArrayElementException() {
    requireArrays();
    requireStrings();
    ArrayFormula<BitvectorFormula, StringFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.getBitvectorTypeWithSize(3), FormulaType.StringType);
    ArrayFormula<BitvectorFormula, StringFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray("a2", FormulaType.getBitvectorTypeWithSize(3), FormulaType.StringType);

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);

    Generator.assembleConstraint(constraint1);
  }

  @Test(expected = GeneratorException.class)
  public void testdeclareArrayIndexException() {
    requireArrays();
    requireStrings();
    ArrayFormula<StringFormula, BitvectorFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.StringType, FormulaType.getBitvectorTypeWithSize(3));
    ArrayFormula<StringFormula, BitvectorFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray("a2", FormulaType.StringType, FormulaType.getBitvectorTypeWithSize(3));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);

    Generator.assembleConstraint(constraint1);
  }

  @Test
  public void testMakeArrayInteger() {
    requireArrays();
    requireIntegers();
    ArrayFormula<IntegerFormula, IntegerFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.IntegerType, FormulaType.IntegerType);
    ArrayFormula<IntegerFormula, IntegerFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray("a2", FormulaType.IntegerType, FormulaType.IntegerType);
    ArrayFormula<
            ArrayFormula<IntegerFormula, IntegerFormula>,
            ArrayFormula<
                ArrayFormula<IntegerFormula, IntegerFormula>,
                ArrayFormula<IntegerFormula, IntegerFormula>>>
        c1 =
            amgr.makeArray(
                "c1",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                        FormulaType.getArrayType(
                            FormulaType.IntegerType, FormulaType.IntegerType))));
    ArrayFormula<
            ArrayFormula<IntegerFormula, IntegerFormula>,
            ArrayFormula<
                ArrayFormula<IntegerFormula, IntegerFormula>,
                ArrayFormula<IntegerFormula, IntegerFormula>>>
        c2 =
            amgr.makeArray(
                "c2",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                        FormulaType.getArrayType(
                            FormulaType.IntegerType, FormulaType.IntegerType))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array Int Int))\n"
            + "(declare-const a2 (Array Int Int))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const c1 (Array (Array Int Int) (Array (Array Int Int) (Array Int Int))))\n"
            + "(declare-const c2 (Array (Array Int Int) (Array (Array Int Int) (Array Int Int))))\n"
            + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayRationals() {
    requireArrays();
    requireRationals();
    ArrayFormula<RationalFormula, RationalFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.RationalType, FormulaType.RationalType);
    ArrayFormula<RationalFormula, RationalFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray("a2", FormulaType.RationalType, FormulaType.RationalType);
    ArrayFormula<
            ArrayFormula<RationalFormula, RationalFormula>,
            ArrayFormula<
                ArrayFormula<RationalFormula, RationalFormula>,
                ArrayFormula<RationalFormula, RationalFormula>>>
        c1 =
            amgr.makeArray(
                "c1",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.RationalType, FormulaType.RationalType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(
                            FormulaType.RationalType, FormulaType.RationalType),
                        FormulaType.getArrayType(
                            FormulaType.RationalType, FormulaType.RationalType))));
    ArrayFormula<
            ArrayFormula<RationalFormula, RationalFormula>,
            ArrayFormula<
                ArrayFormula<RationalFormula, RationalFormula>,
                ArrayFormula<RationalFormula, RationalFormula>>>
        c2 =
            amgr.makeArray(
                "c2",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.RationalType, FormulaType.RationalType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(
                            FormulaType.RationalType, FormulaType.RationalType),
                        FormulaType.getArrayType(
                            FormulaType.RationalType, FormulaType.RationalType))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array Real Real))\n"
            + "(declare-const a2 (Array Real Real))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const c1 (Array (Array Real Real) (Array (Array Real Real) (Array Real"
            + " Real))))\n"
            + "(declare-const c2 (Array (Array Real Real) (Array (Array Real Real) (Array Real"
            + " Real))))\n"
            + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayBooleans() {
    requireArrays();
    requireBooleanArgumentArrays();
    requireAllSortArrays();
    ArrayFormula<BooleanFormula, BooleanFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.BooleanType, FormulaType.BooleanType);
    ArrayFormula<BooleanFormula, BooleanFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray("a2", FormulaType.BooleanType, FormulaType.BooleanType);
    ArrayFormula<
            ArrayFormula<BooleanFormula, BooleanFormula>,
            ArrayFormula<
                ArrayFormula<BooleanFormula, BooleanFormula>,
                ArrayFormula<BooleanFormula, BooleanFormula>>>
        c1 =
            amgr.makeArray(
                "c1",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                        FormulaType.getArrayType(
                            FormulaType.BooleanType, FormulaType.BooleanType))));
    ArrayFormula<
            ArrayFormula<BooleanFormula, BooleanFormula>,
            ArrayFormula<
                ArrayFormula<BooleanFormula, BooleanFormula>,
                ArrayFormula<BooleanFormula, BooleanFormula>>>
        c2 =
            amgr.makeArray(
                "c2",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                        FormulaType.getArrayType(
                            FormulaType.BooleanType, FormulaType.BooleanType))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array Bool Bool))\n"
            + "(declare-const a2 (Array Bool Bool))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const c1 (Array (Array Bool Bool) (Array (Array Bool Bool) (Array Bool"
            + " Bool))))\n"
            + "(declare-const c2 (Array (Array Bool Bool) (Array (Array Bool Bool) (Array Bool"
            + " Bool))))\n"
            + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayBitvectors() {
    requireArrays();
    requireBitvectors();
    ArrayFormula<BitvectorFormula, BitvectorFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray(
                "a1",
                FormulaType.getBitvectorTypeWithSize(3),
                FormulaType.getBitvectorTypeWithSize(3));
    ArrayFormula<BitvectorFormula, BitvectorFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray(
                "a2",
                FormulaType.getBitvectorTypeWithSize(3),
                FormulaType.getBitvectorTypeWithSize(3));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);

    Generator.assembleConstraint(constraint1);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array (_ BitVec 3) (_ BitVec 3)))\n"
            + "(declare-const a2 (Array (_ BitVec 3) (_ BitVec 3)))\n"
            + "(assert (= a1 a2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayMixed() {
    requireArrays();
    requireBitvectors();
    requireRationals();
    requireIntegers();
    requireBooleanArgumentArrays();
    ArrayFormula<IntegerFormula, RationalFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.IntegerType, FormulaType.RationalType);
    ArrayFormula<IntegerFormula, RationalFormula> a2 =
        Objects.requireNonNull(amgr)
            .makeArray("a2", FormulaType.IntegerType, FormulaType.RationalType);
    ArrayFormula<BitvectorFormula, BooleanFormula> b1 =
        amgr.makeArray("b1", FormulaType.getBitvectorTypeWithSize(3), FormulaType.BooleanType);
    ArrayFormula<BitvectorFormula, BooleanFormula> b2 =
        amgr.makeArray("b2", FormulaType.getBitvectorTypeWithSize(3), FormulaType.BooleanType);
    ArrayFormula<
            ArrayFormula<IntegerFormula, IntegerFormula>,
            ArrayFormula<
                ArrayFormula<BooleanFormula, BooleanFormula>,
                ArrayFormula<IntegerFormula, BitvectorFormula>>>
        c1 =
            amgr.makeArray(
                "c1",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                        FormulaType.getArrayType(
                            FormulaType.IntegerType, FormulaType.getBitvectorTypeWithSize(3)))));
    ArrayFormula<
            ArrayFormula<IntegerFormula, IntegerFormula>,
            ArrayFormula<
                ArrayFormula<BooleanFormula, BooleanFormula>,
                ArrayFormula<IntegerFormula, BitvectorFormula>>>
        c2 =
            amgr.makeArray(
                "c2",
                FormulaType.getArrayType(
                    FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                    FormulaType.getArrayType(
                        FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                        FormulaType.getArrayType(
                            FormulaType.IntegerType, FormulaType.getBitvectorTypeWithSize(3)))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint2 = amgr.equivalence(b1, b2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint2);
    Generator.assembleConstraint(constraint3);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array Int Real))\n"
            + "(declare-const a2 (Array Int Real))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const b1 (Array (_ BitVec 3) Bool))\n"
            + "(declare-const b2 (Array (_ BitVec 3) Bool))\n"
            + "(assert (= b1 b2))\n"
            + "(declare-const c1 (Array (Array Int Int) (Array (Array Bool Bool) (Array Int (_"
            + " BitVec 3)))))\n"
            + "(declare-const c2 (Array (Array Int Int) (Array (Array Bool Bool) (Array Int (_"
            + " BitVec 3)))))\n"
            + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testStore() {
    requireArrays();
    requireIntegers();
    assume().that(solverToUse()).isNotEqualTo(Solvers.Z3);
    ArrayFormula<IntegerFormula, IntegerFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.IntegerType, FormulaType.IntegerType);

    ArrayFormula<IntegerFormula, IntegerFormula> term1 =
        amgr.store(a1, imgr.makeNumber(3), imgr.makeNumber(2));
    BooleanFormula constraint = amgr.equivalence(a1, term1);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array Int Int))\n" + "(assert (= a1 (store a1 3 2)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testSelect() {
    requireArrays();
    requireIntegers();
    assume().that(solverToUse()).isNotEqualTo(Solvers.Z3);
    ArrayFormula<IntegerFormula, IntegerFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.IntegerType, FormulaType.IntegerType);

    IntegerFormula term1 = amgr.select(a1, imgr.makeNumber(2));
    BooleanFormula constraint = imgr.equal(term1, imgr.makeNumber(5));

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a1 (Array Int Int))\n" + "(assert (= (select a1 2) 5))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
}
