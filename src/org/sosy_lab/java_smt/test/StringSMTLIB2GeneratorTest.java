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

import java.io.IOException;
import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class StringSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {


  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  @Test
  public void testMakeStringVariable()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    StringFormula a = Objects.requireNonNull(smgr).makeVariable("a");
    StringFormula test = Objects.requireNonNull(smgr).makeVariable("test");
    BooleanFormula constraint = smgr.equal(a, test);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a String)\n"
        + "(declare-const test String)\n"
        + "(assert (= a test))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testConcat() {
    requireStrings();
    StringFormula a = smgr.makeVariable("a");
    StringFormula b = smgr.makeVariable("b");
    StringFormula result = smgr.makeVariable("result");
    BooleanFormula constraint = smgr.equal(smgr.concat(a, b), result);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a String)\n"
        + "(declare-const b String)\n"
        + "(declare-const result String)\n"
        + "(assert (= (str.++ a b) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testContains() {
    requireStrings();
    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    StringFormula part = smgr.makeString("part");
    BooleanFormula constraint = smgr.contains(str, part);

    Generator.assembleConstraint(constraint);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const str String)\n"
        + "(assert (str.contains str \"part\"))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIndexOf() {
    requireStrings();
    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    StringFormula part = smgr.makeString("find");
    IntegerFormula startIndex = imgr.makeNumber(0);
    IntegerFormula result = imgr.makeVariable("result");
    Generator.assembleConstraint(imgr.equal(smgr.indexOf(str, part, startIndex), result));
    String actualResult = String.valueOf(Generator.getLines());


    String expectedResult = "(declare-const str String)\n"
        + "(declare-const result Int)\n"
        + "(assert (= (str.indexof str \"find\" 0) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testSubstring() {
    requireStrings();

    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    IntegerFormula startIndex = imgr.makeNumber(2);
    IntegerFormula length = imgr.makeNumber(4);
    StringFormula result = smgr.makeVariable("result");

    Generator.assembleConstraint(smgr.equal(smgr.substring(str, startIndex, length), result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const str String)\n"
        + "(declare-const result String)\n"
        + "(assert (= (str.substr str 2 4) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testReplace() {
    requireStrings();
    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    StringFormula target = smgr.makeString("target");
    StringFormula replacement = smgr.makeString("replace");
    StringFormula result = smgr.makeVariable("result");

    Generator.assembleConstraint(smgr.equal(smgr.replace(str, target, replacement), result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const str String)\n"
        + "(declare-const result String)\n"
        + "(assert (= (str.replace str \"target\" \"replace\") result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testLength() {
    requireStrings();
    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    IntegerFormula result = imgr.makeVariable("result");

    Generator.assembleConstraint(imgr.equal(smgr.length(str), result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const str String)\n"
        + "(declare-const result Int)\n"
        + "(assert (= (str.len str) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testInRegex() {
    requireStrings();
    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    BooleanFormula result = smgr.in(str, smgr.makeRegex(".*test.*"));

    Generator.assembleConstraint(result);

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const str String)\n"
        + "(assert (str.in_re str (re.from_str \".*test.*\")))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testToInteger() {
    requireStrings();
    StringFormula str = Objects.requireNonNull(smgr).makeVariable("str");
    IntegerFormula result = imgr.makeVariable("result");

    Generator.assembleConstraint(imgr.equal(smgr.toIntegerFormula(str), result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const str String)\n"
        + "(declare-const result Int)\n"
        + "(assert (= (str.to_int str) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testToString() {
    requireStrings();
    StringFormula result = Objects.requireNonNull(smgr).makeVariable("result");
    IntegerFormula number = imgr.makeNumber("42");

    Generator.assembleConstraint(smgr.equal(smgr.toStringFormula(number), result));

    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const result String)\n"
        + "(assert (= (int.to_str 42) result))\n";

    assertThat(actualResult).isEqualTo(expectedResult);
  }
}
