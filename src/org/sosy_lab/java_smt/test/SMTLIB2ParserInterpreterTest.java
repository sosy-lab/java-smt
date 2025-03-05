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

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.BinaryModel;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.ParserException;

@SuppressWarnings({"checkstyle:linelength", "AlmostJavadoc"})
public class SMTLIB2ParserInterpreterTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  /* ARRAY CONSTRAINT TESTS. */
  @Test
  public void testMakeArrayInteger()
      throws SolverException, InterruptedException, InvalidConfigurationException, IOException {
    requireArrays();
    requireIntegers();

    String a =
        "(declare-const a1 (Array Int Int))\n"
            + "(declare-const a2 (Array Int Int))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const c1 (Array (Array Int Int) (Array (Array Int Int) (Array Int Int))))\n"
            + "(declare-const c2 (Array (Array Int Int) (Array (Array Int Int) (Array Int Int))))\n"
            + "(assert (= c1 c2))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

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

    BooleanFormula constraint = bmgr.and(amgr.equivalence(a1, a2), amgr.equivalence(c1, c2));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayRationals()
      throws SolverException, InterruptedException, InvalidConfigurationException, IOException {
    requireArrays();
    requireRationals();

    String a =
        "(declare-const a1 (Array Real Real))\n"
            + "(declare-const a2 (Array Real Real))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const c1 (Array (Array Real Real) (Array (Array Real Real) (Array Real"
            + " Real))))\n"
            + "(declare-const c2 (Array (Array Real Real) (Array (Array Real Real) (Array Real"
            + " Real))))\n"
            + "(assert (= c1 c2))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

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

    BooleanFormula constraint = bmgr.and(amgr.equivalence(a1, a2), amgr.equivalence(c1, c2));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayBooleans()
      throws SolverException, InterruptedException, InvalidConfigurationException, IOException {
    requireArrays();
    requireRationals();
    requireBooleanArgumentArrays();

    String a =
        "(declare-const a1 (Array Bool Bool))\n"
            + "(declare-const a2 (Array Bool Bool))\n"
            + "(assert (= a1 a2))\n"
            + "(declare-const c1 (Array (Array Bool Bool) (Array (Array Bool Bool) (Array Bool"
            + " Bool))))\n"
            + "(declare-const c2 (Array (Array Bool Bool) (Array (Array Bool Bool) (Array Bool"
            + " Bool))))\n"
            + "(assert (= c1 c2))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

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

    BooleanFormula constraint = bmgr.and(amgr.equivalence(a1, a2), amgr.equivalence(c1, c2));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeArrayBitvectors()
      throws SolverException, InterruptedException, InvalidConfigurationException, IOException {
    requireArrays();
    requireBitvectors();

    String a =
        "(declare-const a1 (Array (_ BitVec 3) (_ BitVec 3)))\n"
            + "(declare-const a2 (Array (_ BitVec 3) (_ BitVec 3)))\n"
            + "(assert (= a1 a2))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

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

    BooleanFormula constraint = amgr.equivalence(a1, a2);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeMixed()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireBitvectors();
    requireRationals();
    requireIntegers();
    requireBooleanArgumentArrays();

    String a =
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

    BooleanFormula actualResult = mgr.universalParseFromString(a);

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

    BooleanFormula constraint =
        bmgr.and(amgr.equivalence(a1, a2), amgr.equivalence(b1, b2), amgr.equivalence(c1, c2));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testStore()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireIntegers();

    String a = "(declare-const a1 (Array Int Int))\n" + "(assert (= a1 (store a1 3 2)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    ArrayFormula<IntegerFormula, IntegerFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.IntegerType, FormulaType.IntegerType);

    ArrayFormula<IntegerFormula, IntegerFormula> term1 =
        amgr.store(a1, imgr.makeNumber(3), imgr.makeNumber(2));
    BooleanFormula constraint = amgr.equivalence(a1, term1);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testSelect()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireIntegers();

    String a = "(declare-const a1 (Array Int Int))\n" + "(assert (= (select a1 2) 5))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    ArrayFormula<IntegerFormula, IntegerFormula> a1 =
        Objects.requireNonNull(amgr)
            .makeArray("a1", FormulaType.IntegerType, FormulaType.IntegerType);

    IntegerFormula term1 = amgr.select(a1, imgr.makeNumber(2));
    BooleanFormula constraint = imgr.equal(term1, imgr.makeNumber(5));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  /* BOOL CONSTRAINT TESTS */
  @Test
  public void testMakeVariable()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(assert a)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.makeVariable("a");
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeTrue()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(assert true)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.makeTrue();
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeFalse()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(assert false)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.makeFalse();
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testNot()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(assert (not a))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.not(bmgr.makeVariable("a"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testBinaryOr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (or a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.or(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCollectionOr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (or a b c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.or(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testBinaryAnd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (and a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCollectionAnd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (and a b c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testXor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (xor a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.xor(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testEquivalence()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.equivalence(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testImplication()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (=> a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.implication(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIfThenElse()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (ite a b c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.ifThenElse(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testNestedTerms()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const e Bool)\n"
            + "(declare-const c Bool)\n"
            + "(declare-const d Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const f Bool)\n"
            + "(assert (ite (=> (and a e true) a) (xor c d) (= b (or b (and a e true) a f))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.ifThenElse(
            bmgr.implication(
                bmgr.and(
                    bmgr.and(bmgr.makeBoolean(true), bmgr.makeVariable("a")),
                    bmgr.makeVariable("e"),
                    bmgr.makeTrue()),
                bmgr.and(bmgr.makeBoolean(true), bmgr.makeVariable("a"))),
            bmgr.xor(bmgr.makeVariable("c"), bmgr.makeVariable("d")),
            bmgr.equivalence(
                bmgr.or(bmgr.makeVariable("b"), bmgr.makeFalse()),
                bmgr.or(
                    bmgr.or(bmgr.makeVariable("b"), bmgr.makeFalse()),
                    bmgr.and(
                        bmgr.and(bmgr.makeBoolean(true), bmgr.makeVariable("a")),
                        bmgr.makeVariable("e"),
                        bmgr.makeTrue()),
                    bmgr.and(bmgr.makeBoolean(true), bmgr.makeVariable("a")),
                    bmgr.makeVariable("f"))));
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  /* UF CONSTRAINT TESTS */
  @Test
  public void testdeclareUFBoolean()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBooleanUFs();
    requireNoArgumentsInUFs();
    String x =
        "(declare-fun a (Bool) Bool)\n"
            + "(declare-fun b () Bool)\n"
            + "(assert (= (a false) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FunctionDeclaration<BooleanFormula> a =
        fmgr.declareUF("a", FormulaType.BooleanType, FormulaType.BooleanType);
    FunctionDeclaration<BooleanFormula> b =
        fmgr.declareUF("b", FormulaType.BooleanType, new ArrayList<>());

    BooleanFormula c = fmgr.callUF(a, bmgr.makeFalse());
    BooleanFormula d = fmgr.callUF(b);

    BooleanFormula constraint = bmgr.equivalence(c, d);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFInteger()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x =
        "(declare-fun a (Int) Int)\n" + "(declare-fun b () Int)\n" + "(assert (= (a 4) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FunctionDeclaration<IntegerFormula> a =
        fmgr.declareUF("a", FormulaType.IntegerType, FormulaType.IntegerType);
    FunctionDeclaration<IntegerFormula> b =
        fmgr.declareUF("b", FormulaType.IntegerType, new ArrayList<>());

    IntegerFormula c = fmgr.callUF(a, imgr.makeNumber(4));
    IntegerFormula d = fmgr.callUF(b);

    BooleanFormula constraint = imgr.equal(c, d);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFRational()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x =
        "(declare-fun a (Real) Real)\n" + "(declare-fun b () Real)\n" + "(assert (= (a 4.0) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FunctionDeclaration<RationalFormula> a =
        fmgr.declareUF("a", FormulaType.RationalType, FormulaType.RationalType);
    FunctionDeclaration<RationalFormula> b =
        fmgr.declareUF("b", FormulaType.RationalType, new ArrayList<>());

    RationalFormula c = fmgr.callUF(a, Objects.requireNonNull(rmgr).makeNumber(4));
    RationalFormula d = fmgr.callUF(b);

    BooleanFormula constraint = rmgr.equal(c, d);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFBitvectors()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();
    requireNoArgumentsInUFs();

    String x =
        "(declare-fun a ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(declare-fun b () (_ BitVec 4))\n"
            + "(assert (= (a #b0010) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FunctionDeclaration<BitvectorFormula> a =
        fmgr.declareUF(
            "a", FormulaType.getBitvectorTypeWithSize(4), FormulaType.getBitvectorTypeWithSize(4));
    FunctionDeclaration<BitvectorFormula> b =
        fmgr.declareUF("b", FormulaType.getBitvectorTypeWithSize(4), new ArrayList<>());

    BitvectorFormula c = fmgr.callUF(a, Objects.requireNonNull(bvmgr).makeBitvector(4, 2));
    BitvectorFormula d = fmgr.callUF(b);

    BooleanFormula constraint = bvmgr.equal(c, d);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareUFArrays()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireIntegers();

    String x =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(declare-const test (Array (Array Int Int) Int))\n"
            + "(declare-fun b () (Array Int Int))\n"
            + "(assert (constr (a test) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

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

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBoolean()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBooleanUFs();
    requireNoArgumentsInUFs();
    String x =
        "(declare-fun a (Bool) Bool)\n"
            + "(declare-fun b () Bool)\n"
            + "(assert (= (a false) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BooleanFormula a = fmgr.declareAndCallUF("a", FormulaType.BooleanType, bmgr.makeFalse());
    BooleanFormula b = fmgr.declareAndCallUF("b", FormulaType.BooleanType);

    BooleanFormula constraint = bmgr.equivalence(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFInteger()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x =
        "(declare-fun a (Int) Int)\n" + "(declare-fun b () Int)\n" + "(assert (= (a 4) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = fmgr.declareAndCallUF("a", FormulaType.IntegerType, imgr.makeNumber(4));
    IntegerFormula b = fmgr.declareAndCallUF("b", FormulaType.IntegerType);

    BooleanFormula constraint = imgr.equal(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFRational()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x =
        "(declare-fun a (Real) Real)\n" + "(declare-fun b () Real)\n" + "(assert (= (a 4.0) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a =
        fmgr.declareAndCallUF(
            "a", FormulaType.RationalType, Objects.requireNonNull(rmgr).makeNumber(4));
    RationalFormula b = fmgr.declareAndCallUF("b", FormulaType.RationalType);

    BooleanFormula constraint = rmgr.equal(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFBitvectors()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();
    requireNoArgumentsInUFs();

    String x =
        "(declare-fun a ((_ BitVec 4)) (_ BitVec 4))\n"
            + "(declare-fun b () (_ BitVec 4))\n"
            + "(assert (= (a #b0010) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a =
        fmgr.declareAndCallUF(
            "a",
            FormulaType.getBitvectorTypeWithSize(4),
            Objects.requireNonNull(bvmgr).makeBitvector(4, 2));
    BitvectorFormula b =
        fmgr.declareAndCallUF("b", FormulaType.getBitvectorTypeWithSize(4), new ArrayList<>());

    BooleanFormula constraint = bvmgr.equal(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDeclareAndCallUFArrays()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();

    String x =
        "(declare-fun constr ((Array Int Int)(Array Int Int)) Bool)\n"
            + "(declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))\n"
            + "(declare-const test (Array (Array Int Int) Int))\n"
            + "(declare-fun b () (Array Int Int))\n"
            + "(assert (constr (a test) b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

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

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  /* NUMERAL CONSTRAINT TESTS*/

  @Test
  public void testMakeVariableInteger()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(declare-const a Int)\n" + "(declare-const b Int)\n" + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    BooleanFormula constraint = imgr.equal(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeVariableRational()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(declare-const a Real)\n" + "(declare-const b Real)\n" + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    NumeralFormula a = Objects.requireNonNull(rmgr).makeVariable("a");
    NumeralFormula b = rmgr.makeVariable("b");
    BooleanFormula constraint = rmgr.equal(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerMakeNumberEqualsAndAdd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    assume()
        .withMessage("Solver %s always adds zero", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC5, Solvers.CVC4, Solvers.PRINCESS, Solvers.SMTINTERPOL);

    String x = "(assert (= (+ 1 5) (+ 3 2147483647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = imgr.equal(imgr.add(a, b), imgr.add(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalsMakeNumberEqualsAndAdd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();
    assume()
        .withMessage("Solver %s always adds zero", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC5, Solvers.CVC4, Solvers.SMTINTERPOL);

    String x = "(assert (= 1.0 (+ 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint = rmgr.equal(a, rmgr.add(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerSubtract()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (= 1 (- 5 (- 3 2147483647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = imgr.equal(a, imgr.subtract(b, imgr.subtract(c, e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalSubtract()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (= 1.0 (- 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint = rmgr.equal(a, rmgr.subtract(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerNegate()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (= (- (- 5) (- 1)) (- (- 3) (- 2147483647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);
    BooleanFormula constraint =
        imgr.equal(
            imgr.subtract(imgr.negate(b), imgr.negate(a)),
            imgr.subtract(imgr.negate(c), imgr.negate(e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalNegate()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (= (- 1.0) (- (- 3.4) (- 2147483.647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint =
        rmgr.equal(rmgr.negate(a), rmgr.subtract(rmgr.negate(c), rmgr.negate(e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerSum()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (= 2147483647 (+ 1 5 3 2147483647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);
    List<IntegerFormula> d = new ArrayList<>();
    d.add(a);
    d.add(b);
    d.add(c);
    d.add(e);

    BooleanFormula constraint = imgr.equal(e, imgr.sum(d));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalSum()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (= 1.0 (+ 1.0 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    List<NumeralFormula> d = new ArrayList<>();
    d.add(a);
    d.add(c);
    d.add(e);

    BooleanFormula constraint = rmgr.equal(a, rmgr.sum(d));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerDivide()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    assume().that(solverToUse()).isNotEqualTo(Solvers.OPENSMT);

    String x = "(assert (= 1 (div 5 (div 3 2147483647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = imgr.equal(a, imgr.divide(b, imgr.divide(c, e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalDivide()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (= 1.0 (div 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint = rmgr.equal(a, rmgr.divide(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerModulo()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    assume()
        .withMessage("Solver %s does not support modulo. ", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.MATHSAT5);

    String x = "(assert (= 1 (mod 5 (mod 3 2147483647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = imgr.equal(a, imgr.modulo(b, imgr.modulo(c, e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerMultiply()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (= 1 (* 5 (* 3 2147483647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = imgr.equal(a, imgr.multiply(b, imgr.multiply(c, e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalMultiply()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (= 1.0 (* 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint = rmgr.equal(a, rmgr.multiply(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerDistinct()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (distinct 1 5 3 2147483647))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);
    List<IntegerFormula> d = new ArrayList<>();
    d.add(a);
    d.add(b);
    d.add(c);
    d.add(e);

    BooleanFormula constraint = imgr.distinct(d);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalDistinct()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (distinct 1.0 3.4 2147483.647))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    List<NumeralFormula> d = new ArrayList<>();
    d.add(a);
    d.add(c);
    d.add(e);

    BooleanFormula constraint = rmgr.distinct(d);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testEqual()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    String x = "(assert (= 5 5))";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    IntegerFormula a = imgr.makeNumber(5);
    IntegerFormula b = imgr.makeNumber(5);
    BooleanFormula constraint = imgr.equal(a, b);

    assertThat(actualResult).isEqualTo(constraint);
  }

  @Test
  public void testIntegerGreaterThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (and (> 1 5) (> 3 2147483647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = bmgr.and(imgr.greaterThan(a, b), imgr.greaterThan(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalGreaterThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (and (> 1.0 3.4) (> 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);

    BooleanFormula constraint = bmgr.and(rmgr.greaterThan(a, c), rmgr.greaterThan(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerGreaterOrEquals()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (and (>= 1 5) (>= 3 2147483647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = bmgr.and(imgr.greaterOrEquals(a, b), imgr.greaterOrEquals(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalGreaterOrEquals()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (and (>= 1.0 3.4) (>= 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);

    BooleanFormula constraint = bmgr.and(rmgr.greaterOrEquals(a, c), rmgr.greaterOrEquals(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerLessThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (and (< 1 5) (< 3 2147483647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = bmgr.and(imgr.lessThan(a, b), imgr.lessThan(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalLessThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (and (< 1.0 3.4) (< 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);

    BooleanFormula constraint = bmgr.and(rmgr.lessThan(a, c), rmgr.lessThan(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIntegerLessOrEqual()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (and (<= 1 5) (<= 3 2147483647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);

    BooleanFormula constraint = bmgr.and(imgr.lessOrEquals(a, b), imgr.lessOrEquals(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalLessOrEqual()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();

    String x = "(assert (and (<= 1.0 3.4) (<= 3.4 2147483.647)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);

    BooleanFormula constraint = bmgr.and(rmgr.lessOrEquals(a, c), rmgr.lessOrEquals(c, e));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test(expected = ParserException.class)
  public void testIntegerFloor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    // Broken for anything but Princess
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);

    String x = "(assert (= (- (to_int 5) (to_int 1)) (- (to_int 3) (to_int 2147483647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    IntegerFormula a = imgr.makeNumber(1);
    IntegerFormula b = imgr.makeNumber(5);
    IntegerFormula c = imgr.makeNumber("3");
    IntegerFormula e = imgr.makeNumber(2147483647);
    BooleanFormula expectedResult =
        imgr.equal(
            imgr.subtract(imgr.floor(b), imgr.floor(a)),
            imgr.subtract(imgr.floor(c), imgr.floor(e)));

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testRationalFloor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();
    // OpenSMT does not support 'floor'
    assume().that(solverToUse()).isNotEqualTo(Solvers.OPENSMT);

    String x = "(assert (= (to_int 1.0) (- (to_int 3.4) (to_int 2147483.647))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    RationalFormula a = Objects.requireNonNull(rmgr).makeNumber(1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint =
        imgr.equal(rmgr.floor(a), imgr.subtract(rmgr.floor(c), rmgr.floor(e)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  /* BITVEC CONSTRAINT TESTS*/

  @Test
  public void testMakeVariableBV()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 32))\n"
            + "(declare-const b (_ BitVec 32))\n"
            + "(assert (= a (bvadd a b)))\n"
            + "(declare-const c (_ BitVec 5))\n"
            + "(declare-const d (_ BitVec 5))\n"
            + "(assert (= c d))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(32, "a");
    BitvectorFormula b = bvmgr.makeVariable(32, "b");
    BitvectorFormula c = bvmgr.makeVariable(FormulaType.getBitvectorTypeWithSize(5), "c");
    BitvectorFormula d = bvmgr.makeVariable(FormulaType.getBitvectorTypeWithSize(5), "d");
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.add(a, b));
    BooleanFormula constraint2 = bvmgr.equal(c, d);
    BooleanFormula constraint = bmgr.and(constraint1, constraint2);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testAdd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (= #b111111110110 (bvadd #b111111110110 #b000000010100)))\n"
            + "(assert (= #b01010 (bvadd #b01010 #b00000)))\n"
            + "(assert (="
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " (bvadd"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011011010)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula a = bvmgr.makeBitvector(5, 10);
    BitvectorFormula b = bvmgr.makeBitvector(5, 0);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 263255258);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.add(c, d));
    BooleanFormula constraint2 = bvmgr.equal(a, bvmgr.add(a, b));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.add(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint2);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint2, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testNegate()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (= (bvneg #b111111110110) (bvadd (bvneg #b111111110110) (bvneg"
            + " #b000000010100))))\n"
            + "(assert (= (bvneg"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110)"
            + " (bvadd (bvneg"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110)"
            + " (bvneg"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 =
        bvmgr.equal(bvmgr.negate(c), bvmgr.add(bvmgr.negate(c), bvmgr.negate(d)));
    BooleanFormula constraint3 =
        bvmgr.equal(bvmgr.negate(e), bvmgr.add(bvmgr.negate(e), bvmgr.negate(f)));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testSubtract()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (= #b111111110110 (bvsub #b111111110110 #b000000010100)))\n"
            + "(assert (="
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " (bvsub"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.subtract(c, d));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.subtract(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDivide()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();
    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC4);

    String x =
        "(assert (= #b111111110110 (bvsdiv #b111111110110 #b000000010100)))\n"
            + "(assert (="
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " (bvudiv"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.divide(c, d, true));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.divide(e, f, false));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    System.out.println(Generator.getLines());
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testModulo()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (= #b111111110110 (bvsrem #b111111110110 #b000000010100)))\n"
            + "(assert (="
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " (bvurem"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.modulo(c, d, true));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.modulo(e, f, false));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMultiply()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (= #b111111110110 (bvmul #b111111110110 #b000000010100)))\n"
            + "(assert (="
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " (bvmul"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(c, bvmgr.multiply(c, d));
    BooleanFormula constraint3 = bvmgr.equal(e, bvmgr.multiply(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testGreaterThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (bvsgt #b111111110110 #b000000010100))\n"
            + "(assert (bvugt"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.greaterThan(c, d, true);
    BooleanFormula constraint3 = bvmgr.greaterThan(e, f, false);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testGreaterOrEqual()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (bvsge #b111111110110 #b000000010100))\n"
            + "(assert (bvuge"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.greaterOrEquals(c, d, true);
    BooleanFormula constraint3 = bvmgr.greaterOrEquals(e, f, false);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testLessThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (bvslt #b111111110110 #b000000010100))\n"
            + "(assert (bvult"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.lessThan(c, d, true);
    BooleanFormula constraint3 = bvmgr.lessThan(e, f, false);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testLessOrEqual()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (bvsle #b111111110110 #b000000010100))\n"
            + "(assert (bvule"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.lessOrEquals(c, d, true);
    BooleanFormula constraint3 = bvmgr.lessOrEquals(e, f, false);

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testNotBV()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(assert (= (bvnot #b111111110110) (bvnot #b000000010100)))\n"
            + "(assert (= (bvnot"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110)"
            + " (bvnot"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(bvmgr.not(c), bvmgr.not(d));
    BooleanFormula constraint3 = bvmgr.equal(bvmgr.not(e), bvmgr.not(f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testAndBV()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 12))\n"
            + "(assert (= a (bvand #b111111110110 #b000000010100)))\n"
            + "(declare-const b (_ BitVec 100))\n"
            + "(assert (= b (bvand"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(12, "a");
    BitvectorFormula b = bvmgr.makeVariable(100, "b");
    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.and(c, d));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.and(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testOrBV()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 12))\n"
            + "(assert (= a (bvor #b111111110110 #b000000010100)))\n"
            + "(declare-const b (_ BitVec 100))\n"
            + "(assert (= b (bvor"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(12, "a");
    BitvectorFormula b = bvmgr.makeVariable(100, "b");
    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.or(c, d));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.or(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testBVXor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 12))\n"
            + "(assert (= a (bvxor #b111111110110 #b000000010100)))\n"
            + "(declare-const b (_ BitVec 100))\n"
            + "(assert (= b (bvxor"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(12, "a");
    BitvectorFormula b = bvmgr.makeVariable(100, "b");
    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.xor(c, d));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.xor(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testShiftRight()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 12))\n"
            + "(assert (= a (bvashr #b111111110110 #b000000010100)))\n"
            + "(declare-const b (_ BitVec 100))\n"
            + "(assert (= b (bvlshr"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(12, "a");
    BitvectorFormula b = bvmgr.makeVariable(100, "b");
    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.shiftRight(c, d, true));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.shiftRight(e, f, false));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testShiftLeft()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 12))\n"
            + "(assert (= a (bvshl #b111111110110 #b000000010100)))\n"
            + "(declare-const b (_ BitVec 100))\n"
            + "(assert (= b (bvshl"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(12, "a");
    BitvectorFormula b = bvmgr.makeVariable(100, "b");
    BitvectorFormula c = Objects.requireNonNull(bvmgr).makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = Objects.requireNonNull(bvmgr).makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.shiftLeft(c, d));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.shiftLeft(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testConcat()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 24))\n"
            + "(assert (= a (concat #b111111110110 #b000000010100)))\n"
            + "(declare-const b (_ BitVec 200))\n"
            + "(assert (= b (concat"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000001111101100001111010011010110"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(24, "a");
    BitvectorFormula b = bvmgr.makeVariable(200, "b");
    BitvectorFormula c = bvmgr.makeBitvector(12, -10);
    BitvectorFormula d = bvmgr.makeBitvector(12, 20);
    BitvectorFormula e = bvmgr.makeBitvector(100, 263255254);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.concat(c, d));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.concat(e, f));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testExtract()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 6))\n"
            + "(assert (= a ((_ extract 11 6) #b111111110110)))\n"
            + "(declare-const b (_ BitVec 50))\n"
            + "(assert (= b ((_ extract 99 50)"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(6, "a");
    BitvectorFormula b = bvmgr.makeVariable(50, "b");
    BitvectorFormula c = bvmgr.makeBitvector(12, -10);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.extract(c, 11, 6));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.extract(f, 99, 50));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testExtend()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(declare-const a (_ BitVec 18))\n"
            + "(assert (= a ((_ sign_extend 6) #b111111110110)))\n"
            + "(declare-const b (_ BitVec 150))\n"
            + "(assert (= b ((_ zero_extend 50)"
            + " #b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BitvectorFormula a = Objects.requireNonNull(bvmgr).makeVariable(18, "a");
    BitvectorFormula b = bvmgr.makeVariable(150, "b");
    BitvectorFormula c = bvmgr.makeBitvector(12, -10);
    BitvectorFormula f = bvmgr.makeBitvector(100, 0);
    BooleanFormula constraint1 = bvmgr.equal(a, bvmgr.extend(c, 6, true));
    BooleanFormula constraint3 = bvmgr.equal(b, bvmgr.extend(f, 50, false));

    Generator.assembleConstraint(constraint1);
    Generator.assembleConstraint(constraint3);
    BooleanFormula constraint = bmgr.and(constraint1, constraint3);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  /* EXCEPTION TESTS */

  @Test(expected = ParserException.class)
  public void testExceptionAnd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (and 1 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionOr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (or 1 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionXor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (xor 1 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionXor3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (xor true false false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionNot()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (not 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionNot2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (not true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionImplication()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (=> 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionImplication3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (=> false false true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionIfThenElse()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (ite 4 5 6))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionIfThenElse2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (ite true false)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionAdd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (+ true true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionSubtract()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (- true true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionSubtract3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (- 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionDivide()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (div true true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionDivide3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (div 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionMod()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (mod true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionMod3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (mod 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionMultiply()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (* true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionMultiply3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (* 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionDistinct()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (distinct false true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionGreaterThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (> true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionGreaterThan3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (> 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionGreaterOrEqual()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (>= true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionGreaterOrEqual3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (>= 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionLessThan()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (< true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionLessThan3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (< 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionLessOrEquals()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (<= true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionLessOrEqual3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (<= 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionToInt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (to_int true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionToInt2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (to_int 3 4 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVNeg()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvneg false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVNeg2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvneg #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVAdd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvadd true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVAdd3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvadd #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVSub()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsub true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVSub3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsub #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsdiv()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsdiv true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsdiv3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsdiv #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVudiv()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvudiv true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVudiv3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvudiv #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsrem()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvsrem true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsrem3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsrem #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVurem()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvurem true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVurem3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvurem #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVmul()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvmul true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVmul3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvmul #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsgt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvsgt true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsgt3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsgt #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVugt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvugt true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVugt3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvugt #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsge()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvsge true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsge3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsge #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVuge()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvuge true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVuge3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvuge #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVslt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvslt true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVslt3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvslt #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVult()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvult true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVult3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvult #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsle()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvsle true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsle3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvsle #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVule()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvule true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVule3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvule #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVnot()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvnot true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVnot2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvnot #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVand()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvand true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVand3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvand #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvor true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVor3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvor #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVxor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvxor true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVxor3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvxor #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVashr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvashr true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVashr3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvashr #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVlshr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvlshr true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVlshr3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvlshr #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVshl()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bvshl true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVshl3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (bvshl #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVconcat()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (concat true false))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVconcat3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert (concat #b001 #b100 #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVextract()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert ((_ extract true false) #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVextract2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert ((_ extract 1) #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVextract3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert ((_ extract 1 3) true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVzeroExtend()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert ((_ zero_extend true) #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVzeroExtend2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert ((_ zero_extend 4) true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVZeroExtend3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireBitvectors();

    String x = "(assert ((_ zero_extend 4 1) #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsignExtend()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert ((_ sign_extend true) #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsignExtend2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert ((_ sign_extend 4) true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVsignExtend3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x = "(assert ((_ sign_extend 4 1) #b100))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVtoInt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (bv2int true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionBVtoInt2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();
    requireBitvectorToInt();

    String x = "(assert (bv2int #b100 #b100)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionIntToBV()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireBitvectors();

    String x = "(assert (int2bv #b100)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionSelect()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();

    String x = "(declare-const all1 (Array Int Int))\n" + "(assert (select all1 true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionSelect2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (select true 1))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionSelect3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();

    String x = "(declare-const all1 (Array Int Int))\n" + "(assert (select all1 1 5))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionStore()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();

    String x = "(declare-const all1 (Array Int Int))\n" + "(assert (select all1 1 true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionStore2()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (select true 1 3))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionStore3()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();

    String x = "(declare-const all1 (Array Int Int))\n" + "(assert (select all1 1))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionNewSort()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(declare-sort Type 0)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionForAll()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    // MathSAT does not support arrays with Bool arguments
    assume().that(solverToUse()).isNotEqualTo(Solvers.MATHSAT5);

    String x =
        "(declare-fun subtype (Bool Bool) Bool)\n"
            + "(declare-fun array-of (Bool) Bool)\n"
            + "(assert (forall ((x Bool)) (subtype x x)))\n\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionExists()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    // MathSAT does not support arrays with Bool arguments
    assume().that(solverToUse()).isNotEqualTo(Solvers.MATHSAT5);

    String x =
        "(declare-fun subtype (Bool Bool) Bool)\n"
            + "(declare-fun array-of (Bool) Bool)\n"
            + "(assert (exists ((x Bool)) (subtype x x)))\n\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionExclam()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(assert (! (=> p q) :named PQ))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionPop()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(pop 1)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  @Test(expected = ParserException.class)
  public void testExceptionPush()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(push 1)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    assertThat(actualResult).isEqualTo(null);
  }

  /*PARSE MODEL TESTS*/

  @Test
  public void testDefineFunctionBoolEmptyInput()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x = "(define-fun bla () Bool true)\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BooleanFormula constraint = bmgr.makeTrue();

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionBoolWithInput()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBooleanUFs();

    String x = "(define-fun bla ((x Bool)) Bool (= x true))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);

    BooleanFormula constraint = bmgr.makeTrue();

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionInt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(define-fun bla () Int (- 3 4))\n" + "(assert (= bla bla))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    IntegerFormula drei = imgr.makeNumber(3);
    IntegerFormula vier = imgr.makeNumber(4);
    IntegerFormula sub = imgr.subtract(drei, vier);
    BooleanFormula constraint = imgr.equal(sub, sub);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionIntWithInput()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();

    String x = "(define-fun bla ((x Int)) Int (- 3 x))\n" + "(assert (= bla bla))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    IntegerFormula drei = imgr.makeNumber(3);
    IntegerFormula xVar = imgr.makeVariable("x");
    IntegerFormula sub = imgr.subtract(drei, xVar);
    BooleanFormula constraint = imgr.equal(sub, sub);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionReal()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();
    assume().that(solverToUse()).isNotEqualTo(Solvers.OPENSMT);

    String x = "(define-fun bla () Real (- 3 4.0))\n" + "(assert (= bla bla))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    IntegerFormula drei = imgr.makeNumber(3);
    RationalFormula vier = Objects.requireNonNull(rmgr).makeNumber(4.0);
    RationalFormula sub = rmgr.subtract(drei, vier);
    BooleanFormula constraint = rmgr.equal(sub, sub);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionRealWithInput()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireRationals();
    assume().that(solverToUse()).isNotEqualTo(Solvers.OPENSMT);

    String x = "(define-fun bla ((x Real)) Real (- 3 x))\n" + "(assert (= bla bla))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    IntegerFormula drei = imgr.makeNumber(3);
    RationalFormula xVar = Objects.requireNonNull(rmgr).makeVariable("x");
    RationalFormula sub = rmgr.subtract(drei, xVar);
    BooleanFormula constraint = rmgr.equal(sub, sub);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionBitVec()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(define-fun bla () (_ BitVec 5) (bvsub #b10000 #b00001))\n" + "(assert (= bla bla))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    BitvectorFormula first = Objects.requireNonNull(bvmgr).makeBitvector(5, 16);
    BitvectorFormula second = bvmgr.makeBitvector(5, 1);
    BitvectorFormula sub = bvmgr.subtract(first, second);
    BooleanFormula constraint = bvmgr.equal(sub, sub);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionBitVecWithInput()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String x =
        "(define-fun bla ((x (_ BitVec 5))) (_ BitVec 5) (bvsub #b10000 x))\n"
            + "(assert (= bla bla))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    BitvectorFormula first = Objects.requireNonNull(bvmgr).makeBitvector(5, 16);
    BitvectorFormula second = bvmgr.makeVariable(5, "x");
    BitvectorFormula sub = bvmgr.subtract(first, second);
    BooleanFormula constraint = bvmgr.equal(sub, sub);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testDefineFunctionArray()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();

    String x =
        "(declare-const a (Array Int Int))\n"
            + "(define-fun bla () (Array Int Int) a)\n"
            + "(assert (= a a))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);

    ArrayFormula<IntegerFormula, IntegerFormula> a =
        Objects.requireNonNull(amgr)
            .makeArray("a", FormulaType.IntegerType, FormulaType.IntegerType);
    BooleanFormula constraint = amgr.equivalence(a, a);
    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  /* OTHER FUNCTION TESTS*/

  @Test
  public void testLetExpression()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    assume()
        .that(solverToUse())
        .isNoneOf(Solvers.OPENSMT, Solvers.CVC4, Solvers.SMTINTERPOL, Solvers.YICES2);

    String s =
        "(declare-const x Int)\n"
            + "(declare-const y Int)\n"
            + "(declare-const z Int)\n"
            + "(assert (= z (let ((a (* x y)) (b (div a y))) (* a b))))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(s);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");
    BooleanFormula constraint =
        imgr.equal(z, imgr.multiply(imgr.multiply(x, y), imgr.divide(imgr.multiply(x, y), y)));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testBinaryNumber()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String s = "(declare-const x (_ BitVec 3))\n" + "(assert (= x #b110))";
    BooleanFormula actualResult = mgr.universalParseFromString(s);
    BitvectorFormula x = Objects.requireNonNull(bvmgr).makeVariable(3, "x");
    BooleanFormula constraint = bvmgr.equal(x, bvmgr.makeBitvector(3, 6));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testHexNumber()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();

    String s = "(declare-const x (_ BitVec 12))\n" + "(assert (= x #x110))";
    BooleanFormula actualResult = mgr.universalParseFromString(s);
    BitvectorFormula x = Objects.requireNonNull(bvmgr).makeVariable(12, "x");
    BooleanFormula constraint = bvmgr.equal(x, bvmgr.makeBitvector(12, 272));

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  public void clearGenerator() {
    Generator.setIsLoggingEnabled(true);
    Generator.getLines().delete(0, Generator.getLines().length());
    Generator.getRegisteredVariables().clear();
    Generator.getExecutedAggregator().clear();
  }

  /* MODEL TESTS */

  public String modelToString(ImmutableList<Model.ValueAssignment> modelList) {
    StringBuilder out = new StringBuilder();
    out.append("binary model: \n");
    for (int i = 0; i < modelList.size(); i++) {
      out.append(modelList.get(i));
      out.append("\n");
    }

    return String.valueOf(out);
  }

  @Test
  public void testModelBool()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearGenerator();
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);
    String a =
        "(declare-const c Bool)\n"
            + "(declare-const d Bool)\n"
            + "(assert (and (and d d) (and (not c) (not c))))\n";

    BooleanFormula b = mgr.universalParseFromString(a);
    Model.ValueAssignment entry1 =
        new ValueAssignment(
            bmgr.makeVariable("d"),
            bmgr.makeTrue(),
            bmgr.equivalence(bmgr.makeVariable("d"), bmgr.makeTrue()),
            "d",
            "true",
            new ArrayList<>());
    Model.ValueAssignment entry2 =
        new ValueAssignment(
            bmgr.makeVariable("c"),
            bmgr.makeFalse(),
            bmgr.equivalence(bmgr.makeVariable("c"), bmgr.makeFalse()),
            "c",
            "false",
            new ArrayList<>());
    List<Model.ValueAssignment> temp = new ArrayList<>();
    temp.add(entry1);
    temp.add(entry2);
    String expectedResult = modelToString(ImmutableList.copyOf(temp));

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS, ProverOptions.USE_BINARY)) {
      prover.addConstraint(b);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        try (Model model = prover.getModel()) {
          BinaryModel binaryModel = (BinaryModel) model;
          try (binaryModel) {
            String actualResult = modelToString(binaryModel.asList());
            assertThat(actualResult).isEqualTo(expectedResult);
          }
        }
      }
    }
  }

  @Test
  public void testModelBitvector()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireBitvectors();
    clearGenerator();
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);
    String a =
        "(declare-const c (_ BitVec 3))\n"
            + "(declare-const d (_ BitVec 3))\n"
            + "(assert (= (bvadd c #b101) (bvadd d #b101)))\n";

    BooleanFormula b = mgr.universalParseFromString(a);
    Model.ValueAssignment entry1 =
        new ValueAssignment(
            Objects.requireNonNull(bvmgr).makeVariable(3, "d"),
            bvmgr.makeBitvector(3, 7),
            bvmgr.equal(bvmgr.makeVariable(3, "d"), bvmgr.makeBitvector(3, 7)),
            "d",
            bvmgr.makeBitvector(3, 7).toString(),
            new ArrayList<>());
    Model.ValueAssignment entry2 =
        new ValueAssignment(
            bvmgr.makeVariable(3, "c"),
            bvmgr.makeBitvector(3, 7),
            bvmgr.equal(bvmgr.makeVariable(3, "c"), bvmgr.makeBitvector(3, 7)),
            "c",
            bvmgr.makeBitvector(3, 7).toString(),
            new ArrayList<>());
    List<Model.ValueAssignment> temp = new ArrayList<>();
    temp.add(entry1);
    temp.add(entry2);
    String expectedResult = modelToString(ImmutableList.copyOf(temp));

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS, ProverOptions.USE_BINARY)) {
      prover.addConstraint(b);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        try (Model model = prover.getModel()) {
          BinaryModel binaryModel = (BinaryModel) model;
          try (binaryModel) {
            String actualResult = modelToString(binaryModel.asList());
            assertThat(actualResult).isEqualTo(expectedResult);
          }
        }
      }
    }
  }

  @Test
  public void testModelArrayInt()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireIntegers();
    requireArrays();
    requireArrayModel();
    clearGenerator();
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);
    String a =
        "(declare-const c (Array Int Int))\n"
            + "(declare-const d (Array Int Int))\n"
            + "(assert (= c d))\n";

    BooleanFormula b = mgr.universalParseFromString(a);
    Model.ValueAssignment entry2 =
        new ValueAssignment(
            Objects.requireNonNull(amgr)
                .makeArray("c", FormulaType.IntegerType, FormulaType.IntegerType),
            amgr.makeArray("c", FormulaType.IntegerType, FormulaType.IntegerType),
            amgr.equivalence(
                amgr.makeArray("c", FormulaType.IntegerType, FormulaType.IntegerType),
                amgr.makeArray("c", FormulaType.IntegerType, FormulaType.IntegerType)),
            "c",
            "(as const (Array Int Int) 0)",
            new ArrayList<>());
    Model.ValueAssignment entry1 =
        new ValueAssignment(
            amgr.makeArray("d", FormulaType.IntegerType, FormulaType.IntegerType),
            amgr.makeArray("d", FormulaType.IntegerType, FormulaType.IntegerType),
            amgr.equivalence(
                amgr.makeArray("d", FormulaType.IntegerType, FormulaType.IntegerType),
                amgr.makeArray("d", FormulaType.IntegerType, FormulaType.IntegerType)),
            "d",
            "(as const (Array Int Int) 0)",
            new ArrayList<>());
    List<Model.ValueAssignment> temp = new ArrayList<>();
    temp.add(entry1);
    temp.add(entry2);
    String expectedResult = modelToString(ImmutableList.copyOf(temp));

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS, ProverOptions.USE_BINARY)) {
      prover.addConstraint(b);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        try (Model model = prover.getModel()) {
          BinaryModel binaryModel = (BinaryModel) model;
          try (binaryModel) {
            String actualResult = modelToString(binaryModel.asList());
            assertThat(actualResult).isEqualTo(expectedResult);
          }
        }
      }
    }
  }

  @Test
  public void testModelArrayBitVec()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireBitvectors();
    clearGenerator();
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);
    String a =
        "(declare-const c (Array (_ BitVec 32) (_ BitVec 32)))\n"
            + "(declare-const d (Array (_ BitVec 32) (_ BitVec 32)))\n"
            + "(assert (= c d))\n";

    BooleanFormula b = mgr.universalParseFromString(a);
    Model.ValueAssignment entry2 =
        new ValueAssignment(
            Objects.requireNonNull(amgr)
                .makeArray(
                    "c",
                    FormulaType.getBitvectorTypeWithSize(32),
                    FormulaType.getBitvectorTypeWithSize(32)),
            amgr.makeArray(
                "c",
                FormulaType.getBitvectorTypeWithSize(32),
                FormulaType.getBitvectorTypeWithSize(32)),
            amgr.equivalence(
                amgr.makeArray(
                    "c",
                    FormulaType.getBitvectorTypeWithSize(32),
                    FormulaType.getBitvectorTypeWithSize(32)),
                amgr.makeArray(
                    "c",
                    FormulaType.getBitvectorTypeWithSize(32),
                    FormulaType.getBitvectorTypeWithSize(32))),
            "c",
            "(as const (Array (_ BitVec 32) (_ BitVec 32)) mod_cast(0, 4294967295, 0))",
            new ArrayList<>());
    Model.ValueAssignment entry1 =
        new ValueAssignment(
            amgr.makeArray(
                "d",
                FormulaType.getBitvectorTypeWithSize(32),
                FormulaType.getBitvectorTypeWithSize(32)),
            amgr.makeArray(
                "d",
                FormulaType.getBitvectorTypeWithSize(32),
                FormulaType.getBitvectorTypeWithSize(32)),
            amgr.equivalence(
                amgr.makeArray(
                    "d",
                    FormulaType.getBitvectorTypeWithSize(32),
                    FormulaType.getBitvectorTypeWithSize(32)),
                amgr.makeArray(
                    "d",
                    FormulaType.getBitvectorTypeWithSize(32),
                    FormulaType.getBitvectorTypeWithSize(32))),
            "d",
            "(as const (Array (_ BitVec 32) (_ BitVec 32)) mod_cast(0, 4294967295, 0))",
            new ArrayList<>());
    List<Model.ValueAssignment> temp = new ArrayList<>();
    temp.add(entry1);
    temp.add(entry2);
    String expectedResult = modelToString(ImmutableList.copyOf(temp));

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS, ProverOptions.USE_BINARY)) {
      prover.addConstraint(b);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        try (Model model = prover.getModel()) {
          BinaryModel binaryModel = (BinaryModel) model;
          try (binaryModel) {
            String actualResult = modelToString(binaryModel.asList());
            assertThat(actualResult).isEqualTo(expectedResult);
          }
        }
      }
    }
  }

  @Test
  public void testModelArrayBool()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireArrayModel();
    clearGenerator();
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);
    String a =
        "(declare-const c (Array Bool Bool))\n"
            + "(declare-const d (Array Bool Bool))\n"
            + "(assert (= c d))\n";

    BooleanFormula b = mgr.universalParseFromString(a);
    Model.ValueAssignment entry2 =
        new ValueAssignment(
            Objects.requireNonNull(amgr)
                .makeArray("c", FormulaType.BooleanType, FormulaType.BooleanType),
            amgr.makeArray("c", FormulaType.BooleanType, FormulaType.BooleanType),
            amgr.equivalence(
                amgr.makeArray("c", FormulaType.BooleanType, FormulaType.BooleanType),
                amgr.makeArray("c", FormulaType.BooleanType, FormulaType.BooleanType)),
            "c",
            "(as const (Array Bool Bool) true)",
            new ArrayList<>());
    Model.ValueAssignment entry1 =
        new ValueAssignment(
            amgr.makeArray("d", FormulaType.BooleanType, FormulaType.BooleanType),
            amgr.makeArray("d", FormulaType.BooleanType, FormulaType.BooleanType),
            amgr.equivalence(
                amgr.makeArray("d", FormulaType.BooleanType, FormulaType.BooleanType),
                amgr.makeArray("d", FormulaType.BooleanType, FormulaType.BooleanType)),
            "d",
            "(as const (Array Bool Bool) true)",
            new ArrayList<>());
    List<Model.ValueAssignment> temp = new ArrayList<>();
    temp.add(entry1);
    temp.add(entry2);
    String expectedResult = modelToString(ImmutableList.copyOf(temp));

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS, ProverOptions.USE_BINARY)) {
      prover.addConstraint(b);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        try (Model model = prover.getModel()) {
          BinaryModel binaryModel = (BinaryModel) model;
          try (binaryModel) {
            String actualResult = modelToString(binaryModel.asList());
            assertThat(actualResult).isEqualTo(expectedResult);
          }
        }
      }
    }
  }

  @Test
  public void testModelArrayArray()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    requireArrays();
    requireArrayModel();
    clearGenerator();
    assume().that(solverToUse()).isEqualTo(Solvers.PRINCESS);
    String a =
        "(declare-const c (Array (Array Bool Bool) (Array Bool Bool)))\n"
            + "(declare-const d (Array (Array Bool Bool) (Array Bool Bool)))\n"
            + "(assert (= c d))\n";

    BooleanFormula b = mgr.universalParseFromString(a);
    Model.ValueAssignment entry2 =
        new ValueAssignment(
            Objects.requireNonNull(amgr)
                .makeArray(
                    "c",
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType)),
            amgr.makeArray(
                "c",
                FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType)),
            amgr.equivalence(
                amgr.makeArray(
                    "c",
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType)),
                amgr.makeArray(
                    "c",
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType))),
            "c",
            "(as const (Array (Array Bool Bool (Array Bool Bool) (as const (Array Bool Bool)"
                + " true))",
            new ArrayList<>());
    Model.ValueAssignment entry1 =
        new ValueAssignment(
            amgr.makeArray(
                "d",
                FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType)),
            amgr.makeArray(
                "d",
                FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType)),
            amgr.equivalence(
                amgr.makeArray(
                    "d",
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType)),
                amgr.makeArray(
                    "d",
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType),
                    FormulaType.getArrayType(FormulaType.BooleanType, FormulaType.BooleanType))),
            "d",
            "(as const (Array (Array Bool Bool (Array Bool Bool) (as const (Array Bool Bool)"
                + " true))",
            new ArrayList<>());
    List<Model.ValueAssignment> temp = new ArrayList<>();
    temp.add(entry1);
    temp.add(entry2);
    String expectedResult = modelToString(ImmutableList.copyOf(temp));

    try (ProverEnvironment prover =
        context.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS, ProverOptions.USE_BINARY)) {
      prover.addConstraint(b);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        try (Model model = prover.getModel()) {
          BinaryModel binaryModel = (BinaryModel) model;
          try (binaryModel) {
            String actualResult = modelToString(binaryModel.asList());
            assertThat(actualResult).isEqualTo(expectedResult);
          }
        }
      }
    }
  }
}
