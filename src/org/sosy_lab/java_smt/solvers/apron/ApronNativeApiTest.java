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
import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Interval;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Linterm1;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Scalar;
import apron.Tcons1;
import apron.Texpr0BinNode;
import apron.Texpr0Node;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import com.google.common.base.Preconditions;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.checker.units.qual.A;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.internal.AssumptionViolatedException;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;

public class ApronNativeApiTest {

  public static Manager manager = new Polka(false);
  @Test
  public void solverBackendTest() {
  }

  /**
   * This test shows an example where Apron fails to give a correct solution for a set of
   * constraints that should be unsat;
   * This behavior is not unintended, because some domains can not represent exact disjunctions
   * like != (https://github.com/antoinemine/apron/issues/92)
   * @throws ApronException
   */
  @Test
  public void distinctTest() throws ApronException {
    //x,y = 1 and x!=y
    Texpr1VarNode x = new Texpr1VarNode("x");
    Texpr1VarNode y = new Texpr1VarNode("y");
    Texpr1BinNode leftArg = new Texpr1BinNode(Texpr1BinNode.OP_SUB, x,y);
    Environment environment = new Environment(new String[]{"x","y"},new String[]{});
    Tcons1 xIsZero = new Tcons1(environment, Tcons1.EQ,x);
    Tcons1 yIsZero = new Tcons1(environment, Tcons1.EQ,y);
    Tcons1 constraint = new Tcons1(environment,Tcons1.DISEQ,leftArg);
    Abstract1 abstract1 = new Abstract1(manager, new Tcons1[]{xIsZero,yIsZero,constraint});
    Preconditions.checkArgument(!abstract1.isBottom(manager)); //should return isBottom == true,
    // but doesn't!!!
  }

  /**
   * Test that gives an example of how a domain simplifies constraints
   * @throws ApronException
   */
  @Test
  public void addConstraintsTest() throws ApronException {
    // x+x = 0 and x = 0 is added as only one constraints
    Texpr1VarNode x = new Texpr1VarNode("x");
    Texpr1BinNode add = new Texpr1BinNode(Texpr1BinNode.OP_ADD, x, x);
    Environment environment = new Environment(new String[]{"x"},new String[]{});
    Tcons1 isZero = new Tcons1(environment, Tcons1.EQ, add);
    Tcons1 xisZero = new Tcons1(environment, Tcons1.EQ, x);
    Abstract1 abstract1 = new Abstract1(manager, new Tcons1[]{isZero, xisZero});
    assertTrue(abstract1.toTcons(manager).length == 1);
  }

  /**
   *Somehow the hasVar() method does only work for nodes of level 0
   */
  @Test
  public void hasVarTest(){
    //code form github
    Texpr1VarNode x = new Texpr1VarNode("x");
    Environment environment = new Environment(new String[]{"x"},new String[]{});
    System.out.println(x.hasVar("x"));
    Texpr0Node xZero = x.toTexpr0Node(environment);
    System.out.println(xZero.hasDim(environment.dimOfVar("x")));

    //has Texpr1VarNode "x"?
    Texpr1VarNode x1 = new Texpr1VarNode("x");
    Environment environment1 = new Environment(new String[]{"x"},new String[]{});
    assertTrue(!x1.hasVar("x")); //should be true
    Texpr0Node xZero1 = x.toTexpr0Node(environment);
    assertTrue(xZero1.hasDim(environment.dimOfVar("x")));

    //has x+x "x"?
    Texpr1BinNode xPlusx = new Texpr1BinNode(Texpr1BinNode.OP_ADD, x, x);
    assertTrue(!xPlusx.hasVar("x")); //should be true
    Texpr0Node zeroxPlusx = xPlusx.toTexpr0Node(environment);
    assertTrue(zeroxPlusx.hasDim(environment.dimOfVar("x")));
  }

  /**
   * For having the correct behaviour for Integer nodes one has to specify the rounding type
   * (Integer) and rounding direction; otherwise the nodes will be handled as rational-type nodes
   * @throws ApronException
   */
  @Test
  public void integerRoundingTest() throws ApronException {
    // 4 = 4 * 4/3
    Environment environment = new Environment(new String[]{"x"},new String[]{});
    Texpr1CstNode four = new Texpr1CstNode(new MpqScalar(4));
    Texpr1CstNode three = new Texpr1CstNode(new MpqScalar(3));
    Texpr1BinNode div = new Texpr1BinNode(Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT,
        Texpr1Node.RDIR_DOWN,four, three);
    Texpr1BinNode mul = new Texpr1BinNode(Texpr1BinNode.OP_MUL, four, div);
    Texpr1BinNode sub = new Texpr1BinNode(Texpr1BinNode.OP_SUB,
        Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN,four, mul);
    Tcons1 eq = new Tcons1(environment, Tcons1.EQ, sub);
    Abstract1 abstract1 = new Abstract1(manager, new Tcons1[]{eq});
    assertTrue(!abstract1.isBottom(manager));

    // 1 = 2*(1/2)
    Texpr1CstNode one = new Texpr1CstNode(new MpqScalar(1));
    Texpr1CstNode two = new Texpr1CstNode(new MpqScalar(2));
    Texpr1BinNode half = new Texpr1BinNode(Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT,
        Texpr1Node.RDIR_DOWN,one, two);
    Texpr1BinNode mul2 = new Texpr1BinNode(Texpr1BinNode.OP_MUL, two, half);
    Texpr1BinNode sub2 = new Texpr1BinNode(Texpr1BinNode.OP_SUB,
        Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN,one, mul2);
    Tcons1 eq2 = new Tcons1(environment, Tcons1.EQ, sub2);
    Abstract1 abstract2 = new Abstract1(manager, new Tcons1[]{eq2});
    assertTrue(abstract2.isBottom(manager));

    // x = 2*(x/2) and x = 1
    Texpr1VarNode x = new Texpr1VarNode("x");
    Texpr1BinNode xMinusOne = new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1Node.RDIR_DOWN,
        Texpr1Node.RTYPE_INT,x, one );
    Tcons1 eqXisOne = new Tcons1(environment,Tcons1.EQ,xMinusOne);
    Texpr1BinNode xDivTwo = new Texpr1BinNode(Texpr1BinNode.OP_DIV, Texpr1Node.RTYPE_INT,
        Texpr1Node.RDIR_DOWN,x, two);
    Texpr1BinNode twoMul = new Texpr1BinNode(Texpr1BinNode.OP_MUL, two, xDivTwo);
    Texpr1BinNode xSub = new Texpr1BinNode(Texpr1BinNode.OP_SUB,
        Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN,x, twoMul);
    Tcons1 eq3 = new Tcons1(environment, Tcons1.EQ, sub2);
    Abstract1 abstract3 = new Abstract1(manager, new Tcons1[]{eq3,eqXisOne});
    assertTrue(abstract2.isBottom(manager));
  }

}
