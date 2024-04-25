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

package org.sosy_lab.java_smt.solvers.apron;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Lincons1;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.PolkaEq;
import apron.Tcons1;
import apron.Texpr0Node;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import com.google.common.base.Preconditions;
import org.junit.AssumptionViolatedException;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

public class ApronApiTest {

  public static Manager manager = new PolkaEq();

  @BeforeClass
  public static void loadApron() {
    try {
      NativeLibraries.loadLibrary("japron");
      NativeLibraries.loadLibrary("jgmp");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Apron is not available", e);
    }
  }

  @Test
  public void solverBackendTest() {}

  /**
   * Simple Example that shows how to build constraints in Apron.
   *
   * @throws ApronException throws Exception
   */
  @Test
  public void example() throws ApronException {
    Manager pManager = new Polka(false);
    String[] intVars = {"x"};
    String[] realVars = {"y"};

    Environment environment = new Environment(intVars, realVars);
    // x <= 2 and x >= -3
    // x <= 2 --> -x+2 >= 0
    Lincons1 cons1 = new Lincons1(environment);
    cons1.setCoeff("x", new MpqScalar(-1));
    cons1.setCst(new MpqScalar(+2));
    cons1.setKind(Lincons1.SUPEQ);
    // x >= - 3 --> x+3 >= 0
    Lincons1 cons2 = new Lincons1(environment);
    cons2.setCoeff("x", new MpqScalar(1));
    cons2.setCst(new MpqScalar(+3));
    cons2.setKind(Lincons1.SUPEQ);
    Abstract1 abstract1 = new Abstract1(pManager, new Lincons1[] {cons1, cons2});
    assertWithMessage("The domain is not UNSAT for sure.")
        .that(abstract1.isBottom(pManager))
        .isFalse();
  }

  /**
   * This test shows an example where Apron fails to give a correct solution for a set of
   * constraints that should be unsat; This behavior is not unintended, because some domains can not
   * represent exact disjunctions like != (https://github.com/antoinemine/apron/issues/92).
   *
   * @throws ApronException throws exception
   */
  @Test
  public void distinctTest() throws ApronException {
    // x,y = 1 and x!=y
    Texpr1VarNode x = new Texpr1VarNode("x");
    Texpr1VarNode y = new Texpr1VarNode("y");
    Texpr1BinNode leftArg = new Texpr1BinNode(Texpr1BinNode.OP_SUB, x, y);
    Environment environment = new Environment(new String[] {"x", "y"}, new String[] {});
    Tcons1 xIsZero = new Tcons1(environment, Tcons1.EQ, x);
    Tcons1 yIsZero = new Tcons1(environment, Tcons1.EQ, y);
    Tcons1 constraint = new Tcons1(environment, Tcons1.DISEQ, leftArg);
    Abstract1 abstract1 = new Abstract1(manager, new Tcons1[] {xIsZero, yIsZero, constraint});
    Preconditions.checkArgument(!abstract1.isBottom(manager)); // should return isBottom == true,
    // but doesn't!!!
  }

  /**
   * Test that gives an example of how a domain simplifies constraints.
   *
   * @throws ApronException throws exception
   */
  @Test
  public void addConstraintsTest() throws ApronException {
    // x+x = 0 and x = 0 is added as only one constraints
    Texpr1VarNode x = new Texpr1VarNode("x");
    Texpr1BinNode add = new Texpr1BinNode(Texpr1BinNode.OP_ADD, x, x);
    Environment environment = new Environment(new String[] {"x"}, new String[] {});
    Tcons1 isZero = new Tcons1(environment, Tcons1.EQ, add);
    Tcons1 xisZero = new Tcons1(environment, Tcons1.EQ, x);
    Abstract1 abstract1 = new Abstract1(manager, new Tcons1[] {isZero, xisZero});
    assertThat(abstract1.toTcons(manager).length).isEqualTo(1);
  }

  /** Somehow the hasVar() method does only work for nodes of level 0. */
  @Test
  public void hasVarTest() {
    // code form github
    Texpr1VarNode x = new Texpr1VarNode("x");
    Environment environment = new Environment(new String[] {"x"}, new String[] {});
    System.out.println(x.hasVar("x"));
    Texpr0Node xZero = x.toTexpr0Node(environment);
    System.out.println(xZero.hasDim(environment.dimOfVar("x")));

    // has Texpr1VarNode "x"?
    Texpr1VarNode x1 = new Texpr1VarNode("x");
    Environment environment1 = new Environment(new String[] {"x"}, new String[] {"y"});
    assertThat(x1.hasVar("x")).isFalse(); // should be true
    assertThat(x1.hasVar("y")).isFalse();
    Texpr0Node xZero1 = x.toTexpr0Node(environment1);
    assertThat(xZero1.hasDim(environment1.dimOfVar("x"))).isTrue();
    assertThat(xZero1.hasDim(environment1.dimOfVar("y"))).isFalse();

    // has x+x "x"?
    Texpr1BinNode xPlusx = new Texpr1BinNode(Texpr1BinNode.OP_ADD, x, x);
    assertThat(xPlusx.hasVar("x")).isFalse(); // should be true
    Texpr0Node zeroxPlusx = xPlusx.toTexpr0Node(environment);
    assertThat(zeroxPlusx.hasDim(environment.dimOfVar("x"))).isTrue();
  }

  /**
   * For having the correct behaviour for Integer nodes one has to specify the rounding type
   * (Integer) and rounding direction; otherwise the nodes will be handled as rational-type nodes.
   *
   * @throws ApronException throws exception
   */
  @Test
  public void integerRoundingTest() throws ApronException {
    // 4 = 4 * 4/3
    Environment environment = new Environment(new String[] {"x"}, new String[] {});
    Texpr1CstNode four = new Texpr1CstNode(new MpqScalar(4));
    Texpr1CstNode three = new Texpr1CstNode(new MpqScalar(3));
    Texpr1BinNode div =
        new Texpr1BinNode(
            Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, four, three);
    Texpr1BinNode mul = new Texpr1BinNode(Texpr1BinNode.OP_MUL, four, div);
    Texpr1BinNode sub =
        new Texpr1BinNode(
            Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, four, mul);
    Tcons1 eq = new Tcons1(environment, Tcons1.EQ, sub);
    Abstract1 abstract1 = new Abstract1(manager, new Tcons1[] {eq});
    assertThat(abstract1.isBottom(manager)).isFalse();

    // 1 = 2*(1/2)
    Texpr1CstNode one = new Texpr1CstNode(new MpqScalar(1));
    Texpr1CstNode two = new Texpr1CstNode(new MpqScalar(2));
    Texpr1BinNode half =
        new Texpr1BinNode(
            Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, one, two);
    Texpr1BinNode mul2 = new Texpr1BinNode(Texpr1BinNode.OP_MUL, two, half);
    Texpr1BinNode sub2 =
        new Texpr1BinNode(
            Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, one, mul2);
    Tcons1 eq2 = new Tcons1(environment, Tcons1.EQ, sub2);
    Abstract1 abstract2 = new Abstract1(manager, new Tcons1[] {eq2});
    assertThat(abstract2.isBottom(manager)).isTrue();

    // x = 2*(x/2) and x = 1
    Texpr1VarNode x = new Texpr1VarNode("x");
    Texpr1BinNode xMinusOne =
        new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, x, one);
    // x=1
    Tcons1 eqXisOne = new Tcons1(environment, Tcons1.EQ, xMinusOne);
    // x/2
    Texpr1BinNode xDivTwo =
        new Texpr1BinNode(Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, x, two);
    // 2*(x/2)
    Texpr1BinNode twoMul = new Texpr1BinNode(Texpr1BinNode.OP_MUL, two, xDivTwo);
    // x - 2*(x/2)
    Texpr1BinNode xSub =
        new Texpr1BinNode(
            Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, x, twoMul);
    // x-2*(x/2) = 0
    Tcons1 eq3 = new Tcons1(environment, Tcons1.EQ, xSub);
    Abstract1 abstract3 = new Abstract1(manager, new Tcons1[] {eq3, eqXisOne});
    assertThat(abstract3.isBottom(manager)).isFalse(); // isBottom() should be true!

    // a = 10 and b = 5 and a-b = 7*((a-b)/7)
    Environment environment1 = new Environment(new String[] {"a", "b"}, new String[] {});
    Texpr1VarNode a = new Texpr1VarNode("a");
    Texpr1VarNode b = new Texpr1VarNode("b");
    Texpr1CstNode ten = new Texpr1CstNode(new MpqScalar(10));
    Texpr1CstNode five = new Texpr1CstNode(new MpqScalar(5));
    Texpr1CstNode seven = new Texpr1CstNode(new MpqScalar(7));
    // a=10
    Texpr1BinNode aMin10 =
        new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, a, ten);
    Tcons1 aIsTen = new Tcons1(environment1, Tcons1.EQ, aMin10);
    // b=5
    Texpr1BinNode bMin5 =
        new Texpr1BinNode(
            Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, b, five);
    Tcons1 bIsFive = new Tcons1(environment1, Tcons1.EQ, bMin5);
    // a-b
    Texpr1BinNode aMinb =
        new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, a, b);
    // (a-b)/7
    Texpr1BinNode div7 =
        new Texpr1BinNode(
            Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, aMinb, seven);
    // 7*((a-b)/7)
    Texpr1BinNode mul7 =
        new Texpr1BinNode(
            Texpr1BinNode.OP_MUL, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, seven, div7);
    // (a-b)-(7*((a-b)/7)))
    Texpr1BinNode all =
        new Texpr1BinNode(
            Texpr1BinNode.OP_SUB, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, aMinb, mul7);
    // (a-b)-(7*((a-b)/7))) = 0
    Tcons1 eq1 = new Tcons1(environment1, Tcons1.EQ, all);
    Abstract1 abstract11 = new Abstract1(manager, new Tcons1[] {eq1, aIsTen, bIsFive});
    // isBottom() returns true because eq1 is not added
    assertThat(abstract11.isBottom(manager)).isFalse();
  }
}
