// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.Generator;

@SuppressWarnings("checkstyle:linelength")
public class BooleanSMTLIB2GeneratorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig = super.createTestConfigBuilder();
    return newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
  }

  @Test
  public void testMakeVariable() {
    BooleanFormula a = bmgr.makeVariable("a");
    Generator.assembleConstraint(a);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a Bool)\n" + "(assert a)\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeTrue() {
    BooleanFormula a = bmgr.makeTrue();
    Generator.assembleConstraint(a);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(assert true)\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testMakeFalse() {
    BooleanFormula a = bmgr.makeFalse();
    Generator.assembleConstraint(a);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(assert false)\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testNot() {
    BooleanFormula a = bmgr.not(bmgr.makeVariable("a"));
    Generator.assembleConstraint(a);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult = "(declare-const a Bool)\n" + "(assert (not a))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testBinaryOr() {
    BooleanFormula result = bmgr.or(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (or a b))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCollectionOr() {
    BooleanFormula result =
        bmgr.or(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (or a b c))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testBinaryAnd() {
    BooleanFormula result = bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (and a b))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testCollectionAnd() {
    BooleanFormula result =
        bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (and a b c))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testXor() {
    BooleanFormula result = bmgr.xor(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (xor a b))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testEquivalence() {
    BooleanFormula result = bmgr.equivalence(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (= a b))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testImplication() {
    BooleanFormula result = bmgr.implication(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (=> a b))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testIfThenElse() {
    BooleanFormula result =
        bmgr.ifThenElse(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (ite a b c))\n";
    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void testNestedTerms() {
    BooleanFormula term1 = bmgr.and(bmgr.makeBoolean(true), bmgr.makeVariable("a"));
    BooleanFormula term2 = bmgr.and(term1, bmgr.makeVariable("e"), bmgr.makeTrue());
    BooleanFormula term3 = bmgr.or(bmgr.makeVariable("b"), bmgr.makeFalse());
    BooleanFormula term4 = bmgr.or(term3, term2, term1, bmgr.makeVariable("f"));
    BooleanFormula term5 = bmgr.implication(term2, term1);
    BooleanFormula term6 = bmgr.xor(bmgr.makeVariable("c"), bmgr.makeVariable("d"));
    BooleanFormula term7 = bmgr.equivalence(term3, term4);

    BooleanFormula result = bmgr.ifThenElse(term5, term6, term7);

    Generator.assembleConstraint(result);
    String actualResult = String.valueOf(Generator.getLines());

    String expectedResult =
        "(declare-const a Bool)\n"
            + "(declare-const e Bool)\n"
            + "(declare-const c Bool)\n"
            + "(declare-const d Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const f Bool)\n"
            + "(assert (ite (=> (and a e true) a) (xor c d) (= b (or b (and a e true) a f))))\n";
    // Solverless does not support simplification yet. However, the expression is equivalent.
    String expectedResultSolverless =
        "(declare-const a Bool)\n"
            + "(declare-const e Bool)\n"
            + "(declare-const c Bool)\n"
            + "(declare-const d Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const f Bool)\n"
            + "(assert (ite (=> (and (and true a) e true) (and true a)) (xor c d) (= (or b false)"
            + " (or (or b false) (and (and true a) e true) (and true a) f))))\n";
    assertThat(
        actualResult.equals(expectedResult) || actualResult.equals(expectedResultSolverless));
  }
}
