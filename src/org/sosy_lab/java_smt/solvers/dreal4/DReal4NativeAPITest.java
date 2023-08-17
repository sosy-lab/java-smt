// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.dreal4;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.ImmutableList;
import java.util.Arrays;
import java.util.List;
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
    context.declareVariables(formula);
    context.Assert(formula);
    assertThat(context.CheckSat(model)).isFalse();
  }

  @Test
  public void simpleSAT() {
    Formula fTrue = Formula.True();
    Formula formula = dreal.And(fTrue, fTrue);
    context.declareVariables(formula);
    context.Assert(formula);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simlpeEqualUNSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Equal(zero, one));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isFalse();
  }

  @Test
  public void simpleEqualSAT() {
    Expression zero = Expression.Zero();
    Formula f = new Formula(dreal.Equal(zero, zero));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simpleUnEqualUNSAT() {
    Expression zero = Expression.Zero();
    Formula f = new Formula(dreal.NotEqual(zero, zero));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isFalse();
  }

  @Test
  public void simlpeUnEqualSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.NotEqual(zero, one));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simpleAddUNSAT() {
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Equal(dreal.Add(one, one), one));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isFalse();
  }

  @Test
  public void simpleAddSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Equal(dreal.Add(zero, one), one));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simpleMulAddSAT() {
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(dreal.Equal(dreal.Add(x, y), new Expression(4)));
    Formula assertion2 = new Formula(dreal.Equal(dreal.Multiply(x, y), new Expression(4)));
    context.declareVariables(assertion1);
    context.Assert(assertion1);
    context.declareVariables(assertion2);
    context.Assert(assertion2);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simpleMulAddUNSAT() {
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(dreal.Equal(dreal.Add(x, y), new Expression(1)));
    Formula assertion2 = new Formula(dreal.Equal(dreal.Multiply(x, y), new Expression(1)));
    context.declareVariables(assertion1);
    context.Assert(assertion1);
    context.declareVariables(assertion2);
    context.Assert(assertion2);
    assertThat(context.CheckSat(model)).isFalse();
  }

  @Test
  public void simpleRationalSAT() {
    Expression zero = Expression.Zero();
    Expression eightFith = new Expression(dreal.Divide(new Expression(8), new Expression(5)));
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula f = new Formula(dreal.And(dreal.Grater(y, zero), dreal.Grater(x, zero)));
    Formula g = new Formula(dreal.And(dreal.Less(x, eightFith), dreal.Less(y, eightFith)));
    Formula k = new Formula(dreal.And(f, g));
    Formula assertion = new Formula(dreal.And(k, dreal.Equal(dreal.Add(x, y), eightFith)));
    context.declareVariables(assertion);
    context.Assert(assertion);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simpleOrSAT() {
    Expression zero = Expression.Zero();
    Expression one = Expression.One();
    Formula f = new Formula(dreal.Or(dreal.Grater(zero, zero), dreal.Grater(one, zero)));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void simpleOrUNSAT() {
    Expression zero = Expression.Zero();
    Formula f = new Formula(dreal.Or(dreal.Grater(zero, zero), dreal.Grater(zero, zero)));
    context.declareVariables(f);
    context.Assert(f);
    assertThat(context.CheckSat(model)).isFalse();
  }

  @Test
  public void simpleIncrementalSolving() {
    Expression zero = Expression.Zero();
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(dreal.Equal(dreal.Multiply(x, y), dreal.Add(x, y)));
    Formula assertion2 = new Formula(dreal.And(dreal.NotEqual(x, zero), dreal.Equal(y, zero)));
    context.Push(1);
    context.declareVariables(assertion1);
    context.Assert(assertion1);
    assertThat(context.CheckSat(model)).isTrue();
    context.Push(1);
    context.declareVariables(assertion2);
    context.Assert(assertion2);
    assertThat(context.CheckSat(model)).isFalse();
    context.Pop(1);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void programSynthesis() {
    Variable varX = new Variable("x");
    Variable varA = new Variable("a");
    Variable varB = new Variable("b");
    Variable varC = new Variable("c");

    Expression x = new Expression(varX);
    Expression a = new Expression(varA);
    Expression b = new Expression(varB);
    Expression c = new Expression(varC);
    Expression nt = new Expression(-1000.0);
    Expression t = new Expression(1000.0);
    Expression nh = new Expression(-100.0);
    Expression h = new Expression(100.0);

    Formula sndimply =
        new Formula(
            dreal.imply(dreal.GraterEqual(x, c), dreal.Equal(dreal.abs(x), dreal.Multiply(a, x))));
    Formula thrdimply =
        new Formula(dreal.imply(dreal.Less(x, c), dreal.Equal(dreal.abs(x), dreal.Multiply(b, x))));

    Formula nested =
        new Formula(
            dreal.imply(
                dreal.And(dreal.LessEqual(nt, x), dreal.LessEqual(x, t)),
                dreal.And(sndimply, thrdimply)));

    Formula quantified = new Formula(dreal.forall(new Variables(new Variable[] {varX}), nested));

    Formula f1 = new Formula(dreal.And(dreal.LessEqual(nh, a), dreal.LessEqual(a, h)));
    Formula f2 = new Formula(dreal.And(dreal.LessEqual(nh, b), dreal.LessEqual(b, h)));
    Formula f3 = new Formula(dreal.And(dreal.LessEqual(nh, c), dreal.LessEqual(c, h)));

    Formula f1f2 = new Formula(dreal.And(f1, f2));
    Formula f3quantified = new Formula(dreal.And(f3, quantified));

    Formula check = new Formula(dreal.And(f1f2, f3quantified));

    context.declareVariables(check);
    context.Assert(check);
    assertThat(context.CheckSat(model)).isTrue();
  }

  @Test
  public void getQuantifiedVariablesTest() {
    Variable x = new Variable("x");
    Variable y = new Variable("y");
    Variables vars = new Variables(new Variable[] {x, y});
    Formula f = dreal.forall(vars, dreal.Equal(new Expression(x), new Expression(y)));
    List<Long> expected = ImmutableList.of(x.get_hash(), y.get_hash());
    for (Variable var : f.getQuantifiedVariables()) {
      assertThat(expected).contains(var.get_hash());
    }
  }

  @Test
  public void getFreeVariablesTest() {
    Variable x = new Variable("x");
    Variable y = new Variable("y");
    Formula f = new Formula(dreal.Equal(new Expression(x), new Expression(y)));
    List<Long> expected = Arrays.asList(x.get_hash(), y.get_hash());
    for (Variable var : f.getFreeVariables()) {
        assertThat(expected).contains(var.get_hash());
    }
  }

  @Test
  public void getVariablesTest() {
    Variable x = new Variable("x");
    Variable y = new Variable("y");
    Expression exp = new Expression(dreal.Add(new Expression(x), new Expression(y)));
    List<Long> expected = Arrays.asList(x.get_hash(), y.get_hash());
    for (Variable var : exp.getVariables()) {
      assertThat(expected).contains(var.get_hash());
    }
  }

  @Test
  public void getType() {
    Variable x = new Variable("x", Variable.Type.BOOLEAN);
    Variable y = new Variable("y", Variable.Type.INTEGER);
    Variable z = new Variable("z", Variable.Type.CONTINUOUS);
    Variable a = new Variable("a");
    assertThat(x.get_type()).isEqualTo(Variable.Type.BOOLEAN);
    assertThat(y.get_type()).isEqualTo(Variable.Type.INTEGER);
    assertThat(z.get_type()).isEqualTo(Variable.Type.CONTINUOUS);
    assertThat(a.get_type()).isEqualTo(Variable.Type.CONTINUOUS);
  }
}
