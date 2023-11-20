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

import java.io.IOException;
import org.junit.Assert;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Visitor;

public class BooleanSMTLIB2ParserTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  public void clearVisitor() {
    Visitor.variables.clear();
    Visitor.letVariables.clear();
    Visitor.constraints.clear();
  }

  @Test
  public void testMakeVariable()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(assert a)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.makeVariable("a");
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testMakeTrue()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(assert true)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.makeTrue();
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testMakeFalse()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(assert false)\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.makeFalse();
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testNot()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(assert (not a))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.not(bmgr.makeVariable("a"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testBinaryOr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (or a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.or(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testCollectionOr()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (or a b c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.or(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testBinaryAnd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (and a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testCollectionAnd()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (and a b c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testXor()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (xor a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult = bmgr.xor(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testEquivalence()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.equivalence(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testImplication()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a = "(declare-const a Bool)\n" + "(declare-const b Bool)\n" + "(assert (=> a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.implication(bmgr.makeVariable("a"), bmgr.makeVariable("b"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testIfThenElse()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

    String a =
        "(declare-const a Bool)\n"
            + "(declare-const b Bool)\n"
            + "(declare-const c Bool)\n"
            + "(assert (ite a b c))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(a);

    BooleanFormula expectedResult =
        bmgr.ifThenElse(bmgr.makeVariable("a"), bmgr.makeVariable("b"), bmgr.makeVariable("c"));
    Assert.assertEquals(expectedResult, actualResult);
  }

  @Test
  public void testNestedTerms()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {
    clearVisitor();

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
    Assert.assertEquals(expectedResult, actualResult);
  }
}
