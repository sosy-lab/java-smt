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
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.Generator;

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

  @Test
  public void testStringRegexMatch()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (and (str.<= \"a\" a) (str.<= a \"z\")))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    BooleanFormula regexMatch =
        bmgr.and(
            smgr.lessOrEquals(smgr.makeString("a"), a), smgr.lessOrEquals(a, smgr.makeString("z")));

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexInRe()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(assert (str.in_re a (re.++ (str.to_re \"a\") (str.to_re \"b\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.concat(smgr.makeRegex("a"), smgr.makeRegex("b"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexNone()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a re.none))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    BooleanFormula regexMatch = smgr.in(a, smgr.none());

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexAll()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a re.all))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    BooleanFormula regexMatch = smgr.in(a, smgr.all());

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexConcat()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(assert (str.in_re a (re.++ (str.to_re \"a\") (str.to_re \"b\")))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.concat(smgr.makeRegex("a"), smgr.makeRegex("b"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexUnion()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(assert (str.in_re a (re.union (str.to_re \"a\") (str.to_re \"b\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.union(smgr.makeRegex("a"), smgr.makeRegex("b"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexClosure()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a (re.* (str.to_re \"a\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.closure(smgr.makeRegex("a"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexAllChar()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a re.allchar))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    BooleanFormula regexMatch = smgr.in(a, smgr.allChar());

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexIntersection()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(assert (str.in_re a (re.inter (str.to_re \"a\") (str.to_re \"b\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.intersection(smgr.makeRegex("a"), smgr.makeRegex("b"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexComplement()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n" + "(assert (str.in_re a (re.comp (str.to_re \"a\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);
    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.complement(smgr.makeRegex("a"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexDifference()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const a String)\n"
            + "(assert (str.in_re a (re.diff (str.to_re \"a\") (str.to_re \"b\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.difference(smgr.makeRegex("a"), smgr.makeRegex("b"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexCross()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a (re.+ (str.to_re \"a\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.cross(smgr.makeRegex("a"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexOptional()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a (re.opt (str.to_re \"a\"))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.optional(smgr.makeRegex("a"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testRegexRange()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x = "(declare-const a String)\n" + "(assert (str.in_re a (re.range \"a\" \"z\")))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    StringFormula a = smgr.makeVariable("a");
    RegexFormula regex = smgr.range(smgr.makeString("a"), smgr.makeString("z"));
    BooleanFormula regexMatch = smgr.in(a, regex);

    assertThat(actualResult).isEqualTo(regexMatch);
  }

  @Test
  public void testComplexRegex()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireStrings();
    String x =
        "(declare-const X String)\n"
            + "(assert (not (str.in_re X (str.to_re"
            + " \"HXLogOnlyDaemonactivityIterenetFrom:Class\\u{a}\"))))\n"
            + "(assert (not (str.in_re X (re.union (re.++ (str.to_re \"\\u{22}\") (re.* (re.comp"
            + " (str.to_re \"\\u{22}\"))) (str.to_re \"\\u{22}\")) (re.++ (re.opt (str.to_re"
            + " \"\\u{d}\\u{a}\")) (str.to_re \"\\u{a}'\") (re.* (re.comp (str.to_re"
            + " \"\\u{d}\"))))))))\n"
            + "(assert (not (str.in_re X (re.++ (str.to_re \"Download\") (re.+ (re.range \"0\""
            + " \"9\")) (str.to_re \"ocllceclbhs/gth\\u{a}\")))))\n"
            + "(assert (str.in_re X (str.to_re"
            + " \"User-Agent:Host:TeomaBarHost:HoursHost:\\u{a}\")))\n"
            + "(assert (not (str.in_re X (re.++ (str.to_re \"$\") (re.opt (re.* (re.range \"0\""
            + " \"9\"))) (re.opt (str.to_re \",\")) (re.opt (re.* (re.range \"0\" \"9\"))) (re.opt"
            + " (str.to_re \",\")) (re.* (re.range \"0\" \"9\")) (str.to_re \".\") (re.* (re.range"
            + " \"0\" \"9\")) (str.to_re \"\\u{a}\")))))\n"
            + "(check-sat)";

    BooleanFormula parsed = mgr.universalParseFromString(x);
    ProverEnvironment proverEnvironment = context.newProverEnvironment();
    proverEnvironment.addConstraint(parsed);
    assertThat(proverEnvironment.isUnsat()).isFalse();
  }

  @Test
  public void testDeclareUFString()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x =
        "(set-info :license \"https://creativecommons.org/licenses/by/4.0/\")\n"
            + "(set-info :category \"random\")\n"
            + "(set-info :status sat)\n"
            + "\n"
            + "(declare-fun i () String)\n"
            + "(declare-fun b () String)\n"
            + "(declare-fun g () String)\n"
            + "(declare-fun f () String)\n"
            + "(assert (= (str.++  \"cefcdf\" b \"bgcdfedb\" g \"fgafb\" g \"gefdgcbadf\")  (str.++"
            + "  g \"ef\" i \"dcbbf\" g \"f\" g \"bbg\" f \"gefdg\" g \"badf\") ))\n"
            + "(check-sat)\n"
            + "\n"
            + "(exit)";

    BooleanFormula actualResult = mgr.universalParseFromString(x);
    FunctionDeclaration<StringFormula> i =
        mgr.getUFManager().declareUF("i", FormulaType.StringType);
    FunctionDeclaration<StringFormula> b =
        mgr.getUFManager().declareUF("b", FormulaType.StringType);
    FunctionDeclaration<StringFormula> g =
        mgr.getUFManager().declareUF("g", FormulaType.StringType);
    FunctionDeclaration<StringFormula> f =
        mgr.getUFManager().declareUF("f", FormulaType.StringType);
    BooleanFormula constraint =
        smgr.equal(
            smgr.concat(
                smgr.makeString("cefcdf"),
                fmgr.callUF(b),
                smgr.makeString("bgcdfedb"),
                fmgr.callUF(g),
                smgr.makeString("fgafb"),
                fmgr.callUF(g),
                smgr.makeString("gefdgcbadf")),
            smgr.concat(
                fmgr.callUF(g),
                smgr.makeString("ef"),
                fmgr.callUF(i),
                smgr.makeString("dcbbf"),
                fmgr.callUF(g),
                smgr.makeString("f"),
                fmgr.callUF(g),
                smgr.makeString("bbg"),
                fmgr.callUF(f),
                smgr.makeString("gefdg"),
                fmgr.callUF(g),
                smgr.makeString("badf")));

    Generator.assembleConstraint(actualResult);
    System.out.println(Generator.getSMTLIB2String());
    assertThat(actualResult).isEqualTo(constraint);
  }
}
