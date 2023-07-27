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

package org.sosy_lab.java_smt.solvers.dreal4;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public class DReal4NativeAPITest {

  private Context context;
  private Box model;

  @BeforeClass
  public static void loadDReal() {
    try {
      System.loadLibrary("dreal4");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("dReal is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    Config config = new Config();
    model = new Box();
    config.mutable_precision(0.001);
    config.mutable_use_polytope_in_forall(true);
    config.mutable_use_local_optimization(true);

    context = new Context(config);
  }

  @After
  public void exitEnvironment() {
    Context.Exit();
  }

  @Test
  public void simpleUNSAT() {
    Formula fTrue = Formula.True();
    Formula fFalse = Formula.False();
    Formula formula = dreal.And(fTrue, fFalse);
    context.declareVaribales(formula);
    context.Assert(formula);
    assertFalse(context.CheckSat(model));
  }

  @Test
  public void simpleSAT() {
    Formula fTrue = Formula.True();
    Formula formula = dreal.And(fTrue, fTrue);
    context.declareVaribales(formula);
    context.Assert(formula);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simlpeEqualUNSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Equal(zero, one));
    context.declareVaribales(f);
    context.Assert(f);
    assertFalse(context.CheckSat(model));
  }

  @Test
  public void simpleEqualSAT() {
    Expression zero = Expression.Zero();
    Formula f = new Formula(dreal.Equal(zero, zero));
    context.declareVaribales(f);
    context.Assert(f);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simpleUnEqualUNSAT() {
    Expression zero = Expression.Zero();
    Formula f = new Formula(dreal.NotEqual(zero, zero));
    context.declareVaribales(f);
    context.Assert(f);
    assertFalse(context.CheckSat(model));
  }

  @Test
  public void simlpeUnEqualSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.NotEqual(zero, one));
    context.declareVaribales(f);
    context.Assert(f);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simpleAddUNSAT() {
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Equal(dreal.Add(one, one), one));
    context.declareVaribales(f);
    context.Assert(f);
    assertFalse(context.CheckSat(model));
  }

  @Test
  public void simpleAddSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Equal(dreal.Add(zero, one), one));
    context.declareVaribales(f);
    context.Assert(f);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simpleMulAddSAT() {
    Expression one = Expression.One();
    Expression zero = Expression.Zero();
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable(("y")));
    Formula assertion1 = new Formula(dreal.Equal(dreal.Add(x, y), new Expression(4)));
    Formula assertion2 = new Formula(dreal.Equal(dreal.Multiply(x, y), new Expression(4)));
    context.declareVaribales(assertion1);
    context.Assert(assertion1);
    context.declareVaribales(assertion2);
    context.Assert(assertion2);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simpleMulAddUNSAT() {
    Expression one = Expression.One();
    Expression zero = Expression.Zero();
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable(("y")));
    Formula assertion1 = new Formula(dreal.Equal(dreal.Add(x, y), new Expression(1)));
    Formula assertion2 = new Formula(dreal.Equal(dreal.Multiply(x, y), new Expression(1)));
    context.declareVaribales(assertion1);
    context.Assert(assertion1);
    context.declareVaribales(assertion2);
    context.Assert(assertion2);
    assertFalse(context.CheckSat(model));
  }

  @Test
  public void simpleRationalSAT() {
    Expression zero = Expression.Zero();
    Expression eightFith = new Expression(dreal.Divide(new Expression(8), new Expression(5)));
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable(("y")));
    Formula f = new Formula(dreal.And(dreal.Grater(y, zero), dreal.Grater(x, zero)));
    Formula g = new Formula(dreal.And(dreal.Less(x, eightFith), dreal.Less(y, eightFith)));
    Formula k = new Formula(dreal.And(f, g));
    Formula assertion = new Formula(dreal.And(k, dreal.Equal(dreal.Add(x, y), eightFith)));
    context.declareVaribales(assertion);
    context.Assert(assertion);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simpleOrSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Or(dreal.Grater(zero, zero), dreal.Grater(one, zero)));
    context.declareVaribales(f);
    context.Assert(f);
    assertTrue(context.CheckSat(model));
  }

  @Test
  public void simpleOrUNSAT() {
    Expression zero = Expression.Zero();
    Formula f = new Formula(dreal.Or(dreal.Grater(zero, zero), dreal.Grater(zero, zero)));
    context.declareVaribales(f);
    context.Assert(f);
    assertFalse(context.CheckSat(model));
  }

/*  @Test
  public void simpleIncrementalSolving() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Expression threeHalf = new Expression(dreal.Divide(new Expression(3), new Expression(2)));
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(dreal.Equal(dreal.Add(x, y), dreal.Multiply(x, y)));
    Formula assertion2 = new Formula(dreal.Equal(dreal.Add(x, y), threeHalf));
    Formula assertion3 = new Formula(dreal.Equal(dreal.Multiply(x, y), threeHalf));
    context.Push(1);
    context.declareVaribales(assertion1);
    context.Assert(assertion1);
    assertTrue(context.CheckSat(model));
    context.Push(1);
    context.declareVaribales(assertion2);
    context.Assert(assertion2);
    System.out.println(context.CheckSat(new Box()));
  }*/

  @Test
  public void programSynthesis() {
    Variable var_x = new Variable("x");
    Variable var_a = new Variable("a");
    Variable var_b = new Variable("b");
    Variable var_c = new Variable("c");

    Expression x = new Expression(var_x);
    Expression a = new Expression(var_a);
    Expression b = new Expression(var_b);
    Expression c = new Expression(var_c);
    Expression nt = new Expression(-1000.0);
    Expression t = new Expression(1000.0);
    Expression nh = new Expression(-100.0);
    Expression h = new Expression(100.0);

    Formula sndimply = new Formula(dreal.imply(dreal.GraterEqual(x, c), dreal.Equal(dreal.abs(x), dreal.Multiply(a, x))));
    Formula thrdimply = new Formula(dreal.imply(dreal.Less(x, c), dreal.Equal(dreal.abs(x), dreal.Multiply(b, x))));

    Formula nested = new Formula(dreal.imply(dreal.And(dreal.LessEqual(nt, x), dreal.LessEqual(x, t)), dreal.And(sndimply, thrdimply)));

    Formula quantified = new Formula(dreal.forall(new Variables(new Variable[] {var_x}), nested));

    Formula f1 = new Formula(dreal.And(dreal.LessEqual(nh, a), dreal.LessEqual(a, h)));
    Formula f2 = new Formula(dreal.And(dreal.LessEqual(nh, b), dreal.LessEqual(b, h)));
    Formula f3 = new Formula(dreal.And(dreal.LessEqual(nh, c), dreal.LessEqual(c, h)));

    Formula f1f2 = new Formula(dreal.And(f1, f2));
    Formula f3quantified = new Formula(dreal.And(f3, quantified));

    Formula check = new Formula(dreal.And(f1f2, f3quantified));

    context.declareVaribales(check);
    context.Assert(check);
    assertTrue(context.CheckSat(model));
  }

}
