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

import java.util.Arrays;
import apron.*;
import org.junit.Assert;
import org.junit.AssumptionViolatedException;
import org.sosy_lab.common.NativeLibraries;

/**
 * Simple examples about the Apron Library. Inspired by
 * <a href="https://github.com/antoinemine/apron/blob/master/examples/example1.c">...</a>
 */
public class ApronExamples
{
  private static void testBox(Manager pManager) throws ApronException {
    String[] intVars = {"x"};
    String[] realVars = {"y"};

    Environment environment = new Environment(intVars, realVars);
    //x <= 2 and x >= -3
    //x <= 2 --> -x+2 >= 0
    Lincons1 cons1 = new Lincons1(environment);
    cons1.setCoeff("x",new MpqScalar(-1));
    cons1.setCst(new MpqScalar(+2));
    cons1.setKind(Lincons1.SUPEQ);
    //x >= - 3 --> x+3 >= 0
    Lincons1 cons2 = new Lincons1(environment);
    cons2.setCoeff("x",new MpqScalar(1));
    cons2.setCst(new MpqScalar(+3));
    cons2.setKind(Lincons1.SUPEQ);
    Abstract1 abstract1 = new Abstract1(pManager, new Lincons1[]{cons1,cons2});

    // x+x-x=0
    Linterm1 linterm1 = new Linterm1("x",new MpqScalar(1));
    Linterm1 linterm2 = new Linterm1("x",new MpqScalar(1));
    Linterm1 linterm3 = new Linterm1("x",new MpqScalar(-1));
    Linterm1[] terms = new Linterm1[]{linterm3,linterm2,linterm1};
    Linexpr1 linexpr1 = new Linexpr1(environment,terms,new MpqScalar(0));
    Lincons1 cons = new Lincons1(Lincons1.EQ,linexpr1);

    //is x = 1 satisfiable?
    Lincons1 cons3 = new Lincons1(environment);
    cons3.setCoeff("x",new MpqScalar(1));
    cons3.setCst(new MpqScalar(-1));
    cons3.setKind(Lincons1.EQ);
    assert abstract1.satisfy(pManager,cons3);

    //always unsat example, 1 = 0
    Lincons1 cons4 = new Lincons1(environment);
    cons4.setCoeff("x", new MpqScalar(0));
    cons4.setCst(new MpqScalar(1));
    cons4.setKind(Lincons1.EQ);
    Abstract1 abstract2 = new Abstract1(pManager, new Lincons1[]{cons4});
    assert abstract2.isBottom(pManager);

    //Expression-Tree example, 4x+5 > 0
    Texpr1VarNode varNode = new Texpr1VarNode("x");
    Texpr1CstNode four = new Texpr1CstNode(new MpqScalar(4));
    Texpr1CstNode five = new Texpr1CstNode(new MpqScalar(5));
    Texpr1BinNode term = new Texpr1BinNode(Texpr1BinNode.OP_MUL, four, varNode);
    Texpr1BinNode expr = new Texpr1BinNode(Texpr1BinNode.OP_ADD,term, five);
    Tcons1 constraint = new Tcons1(environment,Tcons1.SUP,expr);
    Tcons1[] tcons = new Tcons1[]{constraint};
    Abstract1 abstract13 = new Abstract1(pManager,tcons);
    assert abstract13.isBottom(pManager);

    //Model example
    Interval interval = abstract1.getBound(pManager, "x");
    System.out.println("Whole interval: "+interval.toString());
    Scalar lowerBound = interval.inf();
    System.out.println("Lower bound: "+lowerBound.toString());
    Scalar upperBound = interval.sup();
    String castString = upperBound.toString();
    int castInt = Integer.parseInt(castString);
    System.out.println(castInt);
    System.out.println("Upper bound: "+upperBound.toString());
  }

  public static void main(String[] args) throws ApronException {
    Manager manager = new Polka(false);
    testBox(manager);
  }
}

