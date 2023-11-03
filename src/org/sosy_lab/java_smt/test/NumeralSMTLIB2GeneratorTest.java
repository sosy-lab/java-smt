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

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.ArrayList;
import org.junit.Assert;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.utils.Generators.Generator;


public class NumeralSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0  {

  /** Integer and Rationals not supported by BOOLECTOR
   *  Rationals not supported by PRINCESS
   *  Z3 runs only when executed separately from other solvers
   */

  public void clearGenerator() {
    Generator.lines.delete(0, Generator.lines.length());
    Generator.registeredVariables.clear();
    Generator.executedAggregator.clear();
  }
  @Test
  public void testMakeVariableInteger() {
      clearGenerator();
      IntegerFormula a = imgr.makeVariable("a");
      IntegerFormula b = imgr.makeVariable("b");
      BooleanFormula constraint = imgr.equal(a, b);
      Generator.logAddConstraint(constraint);
      String actualResult = String.valueOf(Generator.lines);

      String expectedResult = "(declare-const a Int)\n"
          + "(declare-const b Int)\n"
          + "(assert (= a b))\n";
      Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testMakeVariableRational() {
    clearGenerator();
    NumeralFormula a = rmgr.makeVariable("a");
    NumeralFormula b = rmgr.makeVariable("b");
    BooleanFormula constraint = rmgr.equal(a, b);
    Generator.logAddConstraint(constraint);
    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(declare-const a Real)\n"
        + "(declare-const b Real)\n"
        + "(assert (= a b))\n";
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testMakeNumberIntegerAndAdd() {
    clearGenerator();
    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);
    BooleanFormula constraint = imgr.equal(a, imgr.add(c, e));
    Generator.logAddConstraint(constraint);
    String actualResult = String.valueOf(Generator.lines);

    String expectedResult = "(assert (= 1 (+ 3 2147483647)))\n";
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testMakeNumberRationalsAndAdd() {
    clearGenerator();
    RationalFormula a = rmgr.makeNumber(-1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint = rmgr.equal(a, rmgr.add(c, e));
    Generator.logAddConstraint(constraint);
    String actualResult = String.valueOf(Generator.lines);

    String expectedResult1 = "(assert (= -1 (+ 17/5 2147483647/1000)))\n";
    String expectedResult2 = "(assert (= (- 1.0) (+ 3.4 2147483.647)))\n";
    String expectedResult3 = "(assert (= (- 1) (+ (/ 17 5) (/ 2147483647 1000))))\n";
    String expectedResult4 = "(assert (= (- 1.0) (+ (/ 17 5) (/ 2147483647 1000))))\n";

    Assert.assertTrue(actualResult.equals(expectedResult1) || actualResult.equals(expectedResult2) || actualResult.equals(expectedResult3) || actualResult.equals(expectedResult4));
  }
}
