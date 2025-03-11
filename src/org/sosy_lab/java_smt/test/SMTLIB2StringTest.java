// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import java.io.IOException;
import java.util.Objects;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

@SuppressWarnings({"CheckReturnValue", "ReturnValueIgnored"})
public class SMTLIB2StringTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Before
  public void setUp() {
    assume().that(smgr).isNotNull();
  }

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  @Test
  public void testDeclareString()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n";
    BooleanFormula actualResult = Objects.requireNonNull(mgr).universalParseFromString(x);

    StringFormula a = Objects.requireNonNull(smgr).makeVariable("a");

    assertThat(actualResult).isNotNull();
    assertThat(a).isNotNull();
  }

  @Test
  public void testMakeString()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (= a \"Hello\"))";

    BooleanFormula parsed = mgr.universalParseFromString(x);
    StringFormula a = smgr.makeVariable("a");
    BooleanFormula constraint = smgr.equal(a, smgr.makeString("Hello"));
    assertThat(parsed).isEqualTo(constraint);
  }

  @Test
  public void testStringEquality()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(declare-const b String)\n" + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    assert smgr != null;
    StringFormula a = smgr.makeVariable("a");
    StringFormula b = smgr.makeVariable("b");

    BooleanFormula constraint = smgr.equal(a, b);

    assertThat(actualResult).isEqualTo(constraint);
  }

  @Test
  public void testStringConcatenation()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
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

  @Test
  public void testStringLength()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(declare-const a String)\n"
            + "(declare-const len Int)\n"
            + "(assert (= len (str.len a)))\n";

    BooleanFormula expectedResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    IntegerFormula len = imgr.makeVariable("len");

    IntegerFormula lengthResult = smgr.length(a);

    BooleanFormula constraint = imgr.equal(len, lengthResult);
    assertThat(constraint).isEqualTo(expectedResult);
  }

  @Test
  public void testStringSubstring()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
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
  public void testStringContains()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
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
  public void testStringPrefix()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(declare-const prefix String)\n"
            + "(assert (str.prefixof prefix a))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula prefix = smgr.makeVariable("prefix");

    BooleanFormula prefixResult = smgr.prefix(prefix, a);

    assertThat(actualResult).isEqualTo(prefixResult);
  }

  @Test
  public void testStringSuffix()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(declare-const suffix String)\n"
            + "(assert (str.suffixof suffix a))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    StringFormula suffix = smgr.makeVariable("suffix");

    BooleanFormula suffixResult = smgr.suffix(suffix, a);

    assertThat(actualResult).isEqualTo(suffixResult);
  }
}
