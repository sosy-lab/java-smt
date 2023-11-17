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

import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.utils.Generators.Generator;


public class ArraySMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /**
   * Integer and Rationals not supported by BOOLECTOR
   * Rationals not supported by PRINCESS
   * Z3 runs only when executed separately from other solvers
   */

  public void clearGenerator() {
    Generator.lines.delete(0, Generator.lines.length());
    Generator.registeredVariables.clear();
    Generator.executedAggregator.clear();
  }

  @Test
  public void testMakeArrayInteger() {
    requireArrays();
    requireIntegers();
    clearGenerator();
    ArrayFormula<IntegerFormula, IntegerFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.IntegerType,
        FormulaType.IntegerType);
    ArrayFormula<IntegerFormula, IntegerFormula> a2 = Objects.requireNonNull(amgr)
        .makeArray("a2", FormulaType.IntegerType,
            FormulaType.IntegerType);
    ArrayFormula<ArrayFormula<IntegerFormula, IntegerFormula>,
        ArrayFormula<ArrayFormula<IntegerFormula, IntegerFormula>,
        ArrayFormula<IntegerFormula, IntegerFormula>>> c1 = amgr.makeArray("c1",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                FormulaType.getArrayType(FormulaType.IntegerType,
                    FormulaType.IntegerType))));
    ArrayFormula<ArrayFormula<IntegerFormula, IntegerFormula>,
        ArrayFormula<ArrayFormula<IntegerFormula, IntegerFormula>,
            ArrayFormula<IntegerFormula, IntegerFormula>>> c2 = amgr.makeArray("c2",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
                FormulaType.getArrayType(FormulaType.IntegerType,
                    FormulaType.IntegerType))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array Int Int))\n"
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
    clearGenerator();
    ArrayFormula<RationalFormula, RationalFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.RationalType,
            FormulaType.RationalType);
    ArrayFormula<RationalFormula, RationalFormula> a2 = Objects.requireNonNull(amgr)
        .makeArray("a2", FormulaType.RationalType,
            FormulaType.RationalType);
    ArrayFormula<ArrayFormula<RationalFormula, RationalFormula>,
        ArrayFormula<ArrayFormula<RationalFormula, RationalFormula>,
            ArrayFormula<RationalFormula, RationalFormula>>> c1 = amgr.makeArray("c1",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.RationalType, FormulaType.RationalType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.RationalType, FormulaType.RationalType),
                FormulaType.getArrayType(FormulaType.RationalType,
                    FormulaType.RationalType))));
    ArrayFormula<ArrayFormula<RationalFormula, RationalFormula>,
        ArrayFormula<ArrayFormula<RationalFormula, RationalFormula>,
            ArrayFormula<RationalFormula, RationalFormula>>> c2 = amgr.makeArray("c2",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.RationalType, FormulaType.RationalType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.RationalType, FormulaType.RationalType),
                FormulaType.getArrayType(FormulaType.RationalType,
                    FormulaType.RationalType))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array Real Real))\n"
        + "(declare-const a2 (Array Real Real))\n"
        + "(assert (= a1 a2))\n"
        + "(declare-const c1 (Array (Array Real Real) (Array (Array Real Real) (Array Real Real))))\n"
        + "(declare-const c2 (Array (Array Real Real) (Array (Array Real Real) (Array Real Real))))\n"
        + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayBooleans() {
    requireArrays();
    clearGenerator();
    ArrayFormula<BooleanFormula, BooleanFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.BooleanType,
            FormulaType.BooleanType);
    ArrayFormula<BooleanFormula, BooleanFormula> a2 = Objects.requireNonNull(amgr)
        .makeArray("a2", FormulaType.BooleanType,
            FormulaType.BooleanType);
    ArrayFormula<ArrayFormula<BooleanFormula, BooleanFormula>,
        ArrayFormula<ArrayFormula<BooleanFormula, BooleanFormula>,
            ArrayFormula<BooleanFormula, BooleanFormula>>> c1 = amgr.makeArray("c1",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.BooleanType,
                    FormulaType.BooleanType))));
    ArrayFormula<ArrayFormula<BooleanFormula, BooleanFormula>,
        ArrayFormula<ArrayFormula<BooleanFormula, BooleanFormula>,
            ArrayFormula<BooleanFormula, BooleanFormula>>> c2 = amgr.makeArray("c2",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.BooleanType,
                    FormulaType.BooleanType))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array Bool Bool))\n"
        + "(declare-const a2 (Array Bool Bool))\n"
        + "(assert (= a1 a2))\n"
        + "(declare-const c1 (Array (Array Bool Bool) (Array (Array Bool Bool) (Array Bool Bool))))\n"
        + "(declare-const c2 (Array (Array Bool Bool) (Array (Array Bool Bool) (Array Bool Bool))))\n"
        + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayBitvectors() {
    requireArrays();
    requireBitvectors();
    clearGenerator();
    ArrayFormula<BitvectorFormula, BitvectorFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.getBitvectorTypeWithSize(3),
            FormulaType.getBitvectorTypeWithSize(3));
    ArrayFormula<BitvectorFormula, BitvectorFormula> a2 = Objects.requireNonNull(amgr)
        .makeArray("a2", FormulaType.getBitvectorTypeWithSize(3),
            FormulaType.getBitvectorTypeWithSize(3));
    ArrayFormula<ArrayFormula<BitvectorFormula, BitvectorFormula>,
        ArrayFormula<ArrayFormula<BitvectorFormula, BitvectorFormula>,
            ArrayFormula<BitvectorFormula, BitvectorFormula>>> c1 = amgr.makeArray("c1",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.getBitvectorTypeWithSize(3), FormulaType.getBitvectorTypeWithSize(3)),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.getBitvectorTypeWithSize(3), FormulaType.getBitvectorTypeWithSize(3)),
                FormulaType.getArrayType(FormulaType.getBitvectorTypeWithSize(3),
                    FormulaType.getBitvectorTypeWithSize(3)))));
    ArrayFormula<ArrayFormula<BitvectorFormula, BitvectorFormula>,
        ArrayFormula<ArrayFormula<BitvectorFormula, BitvectorFormula>,
            ArrayFormula<BitvectorFormula, BitvectorFormula>>> c2 = amgr.makeArray("c2",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.getBitvectorTypeWithSize(3), FormulaType.getBitvectorTypeWithSize(3)),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.getBitvectorTypeWithSize(3), FormulaType.getBitvectorTypeWithSize(3)),
                FormulaType.getArrayType(FormulaType.getBitvectorTypeWithSize(3),
                    FormulaType.getBitvectorTypeWithSize(3)))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array (_ BitVec 3) (_ BitVec 3)))\n"
        + "(declare-const a2 (Array (_ BitVec 3) (_ BitVec 3)))\n"
        + "(assert (= a1 a2))\n"
        + "(declare-const c1 (Array (Array (_ BitVec 3) (_ BitVec 3)) (Array (Array (_ BitVec 3) (_ BitVec 3)) (Array (_ BitVec 3) (_ BitVec 3)))))\n"
        + "(declare-const c2 (Array (Array (_ BitVec 3) (_ BitVec 3)) (Array (Array (_ BitVec 3) (_ BitVec 3)) (Array (_ BitVec 3) (_ BitVec 3)))))\n"
        + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayMixed() {
    requireArrays();
    requireBitvectors();
    requireRationals();
    requireIntegers();
    clearGenerator();
    ArrayFormula<IntegerFormula, RationalFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.IntegerType,
            FormulaType.RationalType);
    ArrayFormula<IntegerFormula, RationalFormula> a2 = Objects.requireNonNull(amgr)
        .makeArray("a2", FormulaType.IntegerType,
            FormulaType.RationalType);
    ArrayFormula<BitvectorFormula, BooleanFormula> b1 = amgr.makeArray("b1",
        FormulaType.getBitvectorTypeWithSize(3), FormulaType.BooleanType);
    ArrayFormula<BitvectorFormula, BooleanFormula> b2 = amgr.makeArray("b2",
        FormulaType.getBitvectorTypeWithSize(3), FormulaType.BooleanType);
    ArrayFormula<ArrayFormula<IntegerFormula, IntegerFormula>,
        ArrayFormula<ArrayFormula<BooleanFormula, BooleanFormula>,
            ArrayFormula<IntegerFormula, BitvectorFormula>>> c1 = amgr.makeArray("c1",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.IntegerType,
                    FormulaType.getBitvectorTypeWithSize(3)))));
    ArrayFormula<ArrayFormula<IntegerFormula, IntegerFormula>,
        ArrayFormula<ArrayFormula<BooleanFormula, BooleanFormula>,
            ArrayFormula<IntegerFormula, BitvectorFormula>>> c2 = amgr.makeArray("c2",
        FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType),
            FormulaType.getArrayType(FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.IntegerType,
                    FormulaType.getBitvectorTypeWithSize(3)))));

    BooleanFormula constraint1 = amgr.equivalence(a1, a2);
    BooleanFormula constraint2 = amgr.equivalence(b1, b2);
    BooleanFormula constraint3 = amgr.equivalence(c1, c2);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint2);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array Int Real))\n"
        + "(declare-const a2 (Array Int Real))\n"
        + "(assert (= a1 a2))\n"
        + "(declare-const b1 (Array (_ BitVec 3) Bool))\n"
        + "(declare-const b2 (Array (_ BitVec 3) Bool))\n"
        + "(assert (= b1 b2))\n"
        + "(declare-const c1 (Array (Array Int Int) (Array (Array Bool Bool) (Array Int (_ BitVec 3)))))\n"
        + "(declare-const c2 (Array (Array Int Int) (Array (Array Bool Bool) (Array Int (_ BitVec 3)))))\n"
        + "(assert (= c1 c2))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testStore() {
    requireArrays();
    requireIntegers();
    clearGenerator();
    ArrayFormula<IntegerFormula, IntegerFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.IntegerType,
            FormulaType.IntegerType);

    ArrayFormula<IntegerFormula, IntegerFormula> term1 = amgr.store(a1, imgr.makeNumber(3), imgr.makeNumber(2));
    BooleanFormula constraint = amgr.equivalence(a1, term1);

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array Int Int))\n"
        + "(assert (= a1 (store a1 3 2)))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testSelect() {
    requireArrays();
    requireIntegers();
    clearGenerator();
    ArrayFormula<IntegerFormula, IntegerFormula> a1 = Objects.requireNonNull(amgr)
        .makeArray("a1", FormulaType.IntegerType,
            FormulaType.IntegerType);


    IntegerFormula term1 = amgr.select(a1, imgr.makeNumber(2));
    BooleanFormula constraint = imgr.equal(term1, imgr.makeNumber(5));

    Generator.logAddConstraint(constraint);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a1 (Array Int Int))\n"
        + "(assert (= (select a1 2) 5))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
}