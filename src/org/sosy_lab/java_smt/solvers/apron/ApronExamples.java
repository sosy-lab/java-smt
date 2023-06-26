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
    String[] realVars = {};

    Environment environment = new Environment(intVars, realVars);
    //x <= 2 and x >= -3

    //x <= 2 --> -x+2 >= 0
    Lincons1 cons1 = new Lincons1(environment);
    cons1.setCoeff("x",new MpqScalar(-1));
    cons1.setCst(new MpqScalar(+2));
    cons1.setKind(Lincons1.SUPEQ);
    //x >= 3 --> x-3 >= 0
    Lincons1 cons2 = new Lincons1(environment);
    cons2.setCoeff("x",new MpqScalar(1));
    cons2.setCst(new MpqScalar(-3));
    cons2.setKind(Lincons1.SUPEQ);

    Lincons1[] constraints = {cons1, cons2};
    Abstract1 abstract1 = new Abstract1(pManager, constraints);
    //is x = 1 satisfiable?
    Lincons1 cons3 = new Lincons1(environment);
    cons3.setCoeff("x",new MpqScalar(1));
    cons3.setCst(new MpqScalar(-1));
    cons3.setKind(Lincons1.EQ);
    System.out.println("Constraint is satisfiable: "+abstract1.satisfy(pManager, cons3));

    //always unsat example, 1 = 0
    Lincons1 cons4 = new Lincons1(environment);
    cons4.setCoeff("x", new MpqScalar(0));
    cons4.setCst(new MpqScalar(1));
    cons4.setKind(Lincons1.EQ);
    Abstract1 abstract2 = new Abstract1(pManager, new Lincons1[]{cons4});
    System.out.println("Abstract-Obj. is Bottom: "+abstract2.isBottom(pManager));
  }

  public static void main(String[] args) throws ApronException {
    Manager manager = new Box();
    testBox(manager);
  }
}

