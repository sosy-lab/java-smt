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
import static org.junit.Assert.assertThrows;

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
import apron.Texpr0Node;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1VarNode;
import com.google.common.base.Preconditions;
import org.checkerframework.checker.units.qual.A;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.internal.AssumptionViolatedException;
import org.sosy_lab.common.NativeLibraries;

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
    Preconditions.checkArgument(abstract1.isBottom(manager));
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
    Preconditions.checkArgument(abstract1.toTcons(manager).length == 1);
  }

  @Test
  public void hasVarTest(){
    //TODO!!!!!!!!!!!!!
  }

}
