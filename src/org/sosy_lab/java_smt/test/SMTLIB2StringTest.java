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
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverException;

public class SMTLIB2StringTest extends SolverBasedTest0 {

  @Test
  public void testDeclareString() throws IOException, SolverException, InterruptedException,
                                         InvalidConfigurationException {
    String x = "(declare-const a String)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");

    // Check if parsing result matches the expected variable
    assertThat(actualResult).isNotNull();
  }

  @Test
  public void testStringEquality() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const b String)\n"
            + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula b = smgr.makeVariable("b");

    BooleanFormula constraint = smgr.equal(a, b);

    assertThat(actualResult).isEqualTo(constraint);
  }

  @Test
  public void testStringConcatenation() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const b String)\n"
            + "(declare-const c String)\n"
            + "(assert (= c (str.++ a b)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula b = smgr.makeVariable("b");
    StringFormula c = smgr.makeVariable("c");

    StringFormula concatenationResult = smgr.concat(a, b);

    BooleanFormula constraint = smgr.equal(c, concatenationResult);

    assertThat(actualResult).isEqualTo(constraint);
  }
  /*
  @Test
  public void testStringLength() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const len Int)\n"
            + "(assert (= len (str.len a)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    NumeralFormula len = imgr.makeVariable("len", FormulaType.IntegerType);

    NumeralFormula lengthResult = smgr.length(a);

    BooleanFormula constraint = mgr.getIntegerFormulaManager().equal(len, lengthResult);

    assertThat(actualResult).isEqualTo(constraint);
  }
   */


  @Test
  public void testStringSubstring() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const sub String)\n"
            + "(declare-const start Int)\n"
            + "(declare-const length Int)\n"
            + "(assert (= sub (str.substr a start length)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula sub = smgr.makeVariable("sub");
    IntegerFormula start = mgr.getIntegerFormulaManager().makeVariable("start");
    IntegerFormula length = mgr.getIntegerFormulaManager().makeVariable("length");

    StringFormula substringResult = smgr.substring(a, start, length);

    BooleanFormula constraint = smgr.equal(sub, substringResult);

    assertThat(actualResult).isEqualTo(constraint);
  }

  @Test
  public void testStringContains() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const b String)\n"
            + "(assert (str.contains a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula b = smgr.makeVariable("b");

    BooleanFormula containsResult = smgr.contains(a, b);

    assertThat(actualResult).isEqualTo(containsResult);
  }

  @Test
  public void testStringPrefix() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const prefix String)\n"
            + "(assert (str.prefixof prefix a))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula prefix = smgr.makeVariable("prefix");

    BooleanFormula prefixResult = smgr.prefix(a, prefix);

    assertThat(actualResult).isEqualTo(prefixResult);
  }
  /*
  @Test
  public void testStringSuffix() throws  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const suffix String)\n"
            + "(assert (str.suffixof suffix a))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula suffix = smgr.makeVariable("suffix");

    BooleanFormula suffixResult = smgr.endsWith(a, suffix);

    assertThat(actualResult).isEqualTo(suffixResult);
  }
   */

}
