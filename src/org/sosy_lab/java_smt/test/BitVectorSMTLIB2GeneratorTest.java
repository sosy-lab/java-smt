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
import org.junit.Assert;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.utils.Generators.Generator;


public class BitVectorSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

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
  public void testMakeVariable() {
    requireBitvectors();
    clearGenerator();
    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(32, "a");
    BitvectorFormula b = bvmgr.makeVariable(32, "b");
    BitvectorFormula c = bvmgr.makeVariable(FormulaType.getBitvectorTypeWithSize(5), "c");
    BitvectorFormula d = bvmgr.makeVariable(FormulaType.getBitvectorTypeWithSize(5), "d");
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.add(a, b));
    BooleanFormula constraint2 = bvmgr.equal(c, d);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint2);

    /*
     avoid such high numbers with Boolector and Princess
    BitvectorFormula e = bvmgr.makeVariable(214748366, "e");
    BitvectorFormula f = bvmgr.makeVariable(214748366, "f");
    BooleanFormula constraint3 = bvmgr.equal(e, f);
    Generator.logAddConstraint(constraint3);
    */

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult =
        "(declare-const a (_ BitVec 32))\n"
            + "(declare-const b (_ BitVec 32))\n"
            + "(assert (= a (bvadd a b)))\n"
            + "(declare-const c (_ BitVec 5))\n"
            + "(declare-const d (_ BitVec 5))\n"
            + "(assert (= c d))\n";
    // + "(declare-const e (_ BitVec 214748366))\n"
    // + "(declare-const f (_ BitVec 214748366))\n"
    // + "(assert (= e f))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
    }

  @Test
  public void testMakeBitVector() {
    // Not working for Boolector and Yices because of the use of IntegerFormulas,
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula a = bvmgr.makeBitvector(5, imgr.makeNumber(10));
    BitvectorFormula b = bvmgr.makeBitvector(5, imgr.makeNumber(10));
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 263255258);
    BooleanFormula constraint1 = bvmgr.equal(c, d);
    BooleanFormula constraint2 = bvmgr.equal(a, b);
    BooleanFormula constraint3 = bvmgr.equal(e, f);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint2);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultMathsat5 = "(assert (= #b111111110110 #b000000010100))\n"
        + "(assert (= #b01010 #b01010))\n"
        + "(assert (= #b111111110110 #b000000010100))\n";
    String expectedResultOthers = "(assert (= #b111111110110 #b000000010100))\n"
        + "(assert (= #b01010 #b01010))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011011010))\n";
    Assert.assertTrue(expectedResultMathsat5.equals(actualResult) || expectedResultOthers.equals(actualResult));
  }
  @Test
  public void testAdd() {
    // Not working for Boolector and Yices because of the use of IntegerFormulas,
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula a = bvmgr.makeBitvector(5, imgr.makeNumber(10));
    BitvectorFormula b = bvmgr.makeBitvector(5, imgr.makeNumber(0));
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 263255258);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.add(c, d));
    BooleanFormula constraint2 = bvmgr.equal(a, bvmgr.add(a, b));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.add(e, f));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint2);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultMathsat5 = "(assert (= #b111111110110 (bvadd #b111111110110 #b000000010100)))\n"
        + "(assert (= #b01010 #b01010))\n"
        + "(assert (= #b111111110110 (bvadd #b111111110110 #b000000010100)))\n";
    String expectedResultOthers = "(assert (= #b111111110110 (bvadd #b111111110110 #b000000010100)))\n"
        + "(assert (= #b01010 (bvadd #b01010 #b00000)))\n"
        + "(assert (= "
        +
        "#b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvadd #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011011010)))\n";
    Assert.assertTrue(expectedResultMathsat5.equals(actualResult) || expectedResultOthers.equals(actualResult));
  }

  @Test
  public void testNegate() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(bvmgr.negate(c), bvmgr.add(bvmgr.negate(c),
        bvmgr.negate(d)));
    BooleanFormula constraint3 = bvmgr.equal(bvmgr.negate(e), bvmgr.add(bvmgr.negate(e),
        bvmgr.negate(f)));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultMathsat5 = "(assert (= (bvneg #b111111110110) #b111111110110))\n"
        + "(assert (= (bvneg #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110) (bvneg #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110)))\n";
    String expectedResultOthers = "(assert (= (bvneg #b111111110110) (bvadd (bvneg #b111111110110) (bvneg #b000000010100))))\n"
        + "(assert (= (bvneg #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110) (bvadd (bvneg #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110) (bvneg #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))\n";
    Assert.assertTrue(expectedResultMathsat5.equals(actualResult) || expectedResultOthers.equals(actualResult));
  }

  @Test
  public void testSubtract() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.subtract(c, d));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.subtract(e, f));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultMathsat5 = "(assert (= #b111111110110 (bvsub #b111111110110 #b000000010100)))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110))\n";
    String expectedResultOthers = "(assert (= #b111111110110 (bvsub #b111111110110 #b000000010100)))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvsub #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    Assert.assertTrue(expectedResultMathsat5.equals(actualResult) || expectedResultOthers.equals(actualResult));
  }

  @Test
  public void testDivide() {
    //Does not work for CVC4 due to "BigInteger argument out of bounds"
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.divide(c, d, true));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.divide(e, f, false));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultOthers = "(assert (= #b111111110110 (bvsdiv #b111111110110 "
        + "#b000000010100)))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvudiv #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    String expectedResultYices = "(assert (= #b111111110110 (bvsdiv #b111111110110 "
        + "#b000000010100)))\n"
        + "(assert (= #b111111110110 (bvsdiv #b111111110110 #b000000010100)))\n";
    Assert.assertTrue(expectedResultYices.equals(actualResult) || expectedResultOthers.equals(actualResult));
  }

  @Test
  public void testModulo() {
    //Does not work for CVC4 due to "BigInteger argument out of bounds"
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.modulo(c, d, true));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.modulo(e, f, false));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultOthers = "(assert (= #b111111110110 (bvsrem #b111111110110 #b000000010100)))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvurem #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    String expectedResultYices = "(assert (= #b111111110110 #b111111110110))\n"
        + "(assert (= #b111111110110 #b111111110110))\n";
    String expectedResultMathsat5 = "(assert (= #b111111110110 #b111111110110))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvurem #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    Assert.assertTrue(expectedResultYices.equals(actualResult) || expectedResultOthers.equals(actualResult) || expectedResultMathsat5.equals(actualResult));
  }

  @Test
  public void testMultiply() {
    //Does not work for CVC4 due to "BigInteger argument out of bounds"
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.multiply(c, d));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.multiply(e, f));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultOthers = "(assert (= #b111111110110 (bvmul #b111111110110 "
        + "#b000000010100)))\n"
        + "(assert (= "
        +
        "#b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvmul #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    String expectedResultYices = "(assert (= #b111111110110 #b111111110110))\n"
        + "(assert (= #b111111110110 #b111111110110))\n";
    String expectedResultMathsat5 = "(assert (= #b111111110110 (bvmul #b111111110110 #b000000010100)))\n"
        + "(assert (= #b111111110110 (bvmul #b111111110110 #b000000010100)))\n";
    Assert.assertTrue(expectedResultYices.equals(actualResult) || expectedResultOthers.equals(actualResult) || expectedResultMathsat5.equals(actualResult));
  }

  @Test
  public void testGreaterThan() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.greaterThan(c, d, true);
    BooleanFormula constraint3 = bvmgr.greaterThan(e, f, false);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(assert (bvsgt #b111111110110 #b000000010100))\n"
        + "(assert (bvugt #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testGreaterOrEqual() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.greaterOrEquals(c, d, true);
    BooleanFormula constraint3 = bvmgr.greaterOrEquals(e, f, false);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(assert (bvsge #b111111110110 #b000000010100))\n"
        + "(assert (bvuge "
        + "#b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testLessThan() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.lessThan(c, d, true);
    BooleanFormula constraint3 = bvmgr.lessThan(e, f, false);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(assert (bvslt #b111111110110 #b000000010100))\n"
        + "(assert (bvult "
        + "#b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testLessOrEqual() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.lessOrEquals(c, d, true);
    BooleanFormula constraint3 = bvmgr.lessOrEquals(e, f, false);

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(assert (bvsle #b111111110110 #b000000010100))\n"
        + "(assert (bvule "
        + "#b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testNot() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(bvmgr.not(c), bvmgr.not(d));
    BooleanFormula constraint3 = bvmgr.equal(bvmgr.not(e), bvmgr.not(f));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultMathsat5 = "(assert (= (bvnot #b111111110110) (bvnot #b000000010100)))\n"
        + "(assert (= (bvnot #b111111110110) (bvnot #b000000010100)))\n";
    String expectedResultOthers = "(assert (= (bvnot #b111111110110) (bvnot #b000000010100)))\n"
        + "(assert (= (bvnot #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110) (bvnot #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    Assert.assertTrue(expectedResultMathsat5.equals(actualResult) || expectedResultOthers.equals(actualResult));
  }

  @Test
  public void testAnd() {
    requireBitvectors();
    clearGenerator();

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.and(c, d));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.and(e, f));

    Generator.logAddConstraint(constraint1);
    Generator.logAddConstraint(constraint3);

    String actualResult = String.valueOf(Generator.lines);

    String expectedResultMathsat5 = "(assert (= (bvnot #b111111110110) (bvnot #b000000010100)))\n"
        + "(assert (= (bvnot #b111111110110) (bvnot #b000000010100)))\n";
    String expectedResultOthers = "(assert (= #b111111110110 #b000000010100))\n"
        + "(assert (= #b111111110110 #b000000010100))\n";
    String expectedResultZ3 = "(assert (= #b111111110110 (bvand #b111111110110 #b000000010100)))\n"
        + "(assert (= #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 (bvand #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110 #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";
    Assert.assertTrue(expectedResultMathsat5.equals(actualResult) || expectedResultOthers.equals(actualResult) || expectedResultZ3.equals(actualResult));
  }

  }