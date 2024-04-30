// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

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
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;

public class DReal4NativeAPITest {

  private Context context;
  private Box model;

  @BeforeClass
  public static void loadDReal() {
    try {
      NativeLibraries.loadLibrary("drealjava");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("dReal is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    Config config = new Config();
    model = new Box();
    config.mutablePrecision(0.001);
    config.mutableUsePolytopeInForall(true);
    config.mutableUseLocalOptimization(true);

    context = new Context(config);
  }

  @After
  public void exitEnvironment() {
    Context.exit();
  }

  @Test
  public void simpleUNSAT() {
    Formula fTrue = Formula.formulaTrue();
    Formula fFalse = Formula.formulaFalse();
    Formula formula = Dreal.and(fTrue, fFalse);
    context.declareVariables(formula);
    context.assertion(formula);
    assertThat(context.checkSat(model)).isFalse();
  }

  @Test
  public void simpleSAT() {
    Formula fTrue = Formula.formulaTrue();
    Formula formula = Dreal.and(fTrue, fTrue);
    context.declareVariables(formula);
    context.assertion(formula);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simlpeequalUNSAT() {
    Expression zero = Expression.zero();
    Expression one = Expression.one();
    Formula f = new Formula(Dreal.equal(zero, one));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isFalse();
  }

  @Test
  public void simpleEqualSAT() {
    Expression zero = Expression.zero();
    Formula f = new Formula(Dreal.equal(zero, zero));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simpleUnEqualUNSAT() {
    Expression zero = Expression.zero();
    Formula f = new Formula(Dreal.notEqual(zero, zero));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isFalse();
  }

  @Test
  public void simlpeUnEqualSAT() {
    Expression zero = Expression.zero();
    Expression one = Expression.one();
    Formula f = new Formula(Dreal.notEqual(zero, one));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simpleAddUNSAT() {
    Expression one = Expression.one();
    Formula f = new Formula(Dreal.equal(Dreal.add(one, one), one));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isFalse();
  }

  @Test
  public void simpleAddSAT() {
    Expression zero = Expression.zero();
    Expression one = Expression.one();
    Formula f = new Formula(Dreal.equal(Dreal.add(zero, one), one));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simpleMulAddSAT() {
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(Dreal.equal(Dreal.add(x, y), new Expression(4)));
    Formula assertion2 = new Formula(Dreal.equal(Dreal.multiply(x, y), new Expression(4)));
    context.declareVariables(assertion1);
    context.assertion(assertion1);
    context.declareVariables(assertion2);
    context.assertion(assertion2);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simpleMulAddUNSAT() {
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(Dreal.equal(Dreal.add(x, y), new Expression(1)));
    Formula assertion2 = new Formula(Dreal.equal(Dreal.multiply(x, y), new Expression(1)));
    context.declareVariables(assertion1);
    context.assertion(assertion1);
    context.declareVariables(assertion2);
    context.assertion(assertion2);
    assertThat(context.checkSat(model)).isFalse();
  }

  @Test
  public void simpleRationalSAT() {
    Expression zero = Expression.zero();
    Expression eightFith = new Expression(Dreal.divide(new Expression(8), new Expression(5)));
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula f = new Formula(Dreal.and(Dreal.grater(y, zero), Dreal.grater(x, zero)));
    Formula g = new Formula(Dreal.and(Dreal.less(x, eightFith), Dreal.less(y, eightFith)));
    Formula k = new Formula(Dreal.and(f, g));
    Formula assertion = new Formula(Dreal.and(k, Dreal.equal(Dreal.add(x, y), eightFith)));
    context.declareVariables(assertion);
    context.assertion(assertion);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simpleOrSAT() {
    Expression zero = Expression.zero();
    Expression one = Expression.one();
    Formula f = new Formula(Dreal.or(Dreal.grater(zero, zero), Dreal.grater(one, zero)));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void simpleOrUNSAT() {
    Expression zero = Expression.zero();
    Formula f = new Formula(Dreal.or(Dreal.grater(zero, zero), Dreal.grater(zero, zero)));
    context.declareVariables(f);
    context.assertion(f);
    assertThat(context.checkSat(model)).isFalse();
  }

  @Test
  public void simpleIncrementalSolving() {
    Expression zero = Expression.zero();
    Expression x = new Expression(new Variable("x"));
    Expression y = new Expression(new Variable("y"));
    Formula assertion1 = new Formula(Dreal.equal(Dreal.multiply(x, y), Dreal.add(x, y)));
    Formula assertion2 = new Formula(Dreal.and(Dreal.notEqual(x, zero), Dreal.equal(y, zero)));
    context.push(1);
    context.declareVariables(assertion1);
    context.assertion(assertion1);
    assertThat(context.checkSat(model)).isTrue();
    context.push(1);
    context.declareVariables(assertion2);
    context.assertion(assertion2);
    assertThat(context.checkSat(model)).isFalse();
    context.pop(1);
    assertThat(context.checkSat(model)).isTrue();
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
            Dreal.imply(Dreal.graterEqual(x, c), Dreal.equal(Dreal.abs(x), Dreal.multiply(a, x))));
    Formula thrdimply =
        new Formula(Dreal.imply(Dreal.less(x, c), Dreal.equal(Dreal.abs(x), Dreal.multiply(b, x))));

    Formula nested =
        new Formula(
            Dreal.imply(
                Dreal.and(Dreal.lessEqual(nt, x), Dreal.lessEqual(x, t)),
                Dreal.and(sndimply, thrdimply)));

    Formula quantified = new Formula(Dreal.forall(new Variables(new Variable[] {varX}), nested));

    Formula f1 = new Formula(Dreal.and(Dreal.lessEqual(nh, a), Dreal.lessEqual(a, h)));
    Formula f2 = new Formula(Dreal.and(Dreal.lessEqual(nh, b), Dreal.lessEqual(b, h)));
    Formula f3 = new Formula(Dreal.and(Dreal.lessEqual(nh, c), Dreal.lessEqual(c, h)));

    Formula f1f2 = new Formula(Dreal.and(f1, f2));
    Formula f3quantified = new Formula(Dreal.and(f3, quantified));

    Formula check = new Formula(Dreal.and(f1f2, f3quantified));

    context.declareVariables(check);
    context.assertion(check);
    assertThat(context.checkSat(model)).isTrue();
  }

  @Test
  public void getQuantifiedVariablesTest() {
    Variable x = new Variable("x");
    Variable y = new Variable("y");
    Variables vars = new Variables(new Variable[] {x, y});
    Formula f = Dreal.forall(vars, Dreal.equal(new Expression(x), new Expression(y)));
    List<Long> expected = ImmutableList.of(x.getHash(), y.getHash());
    for (Variable var : f.getQuantifiedVariables()) {
      assertThat(expected).contains(var.getHash());
    }
  }

  @Test
  public void getFreeVariablesTest() {
    Variable x = new Variable("x");
    Variable y = new Variable("y");
    Formula f = new Formula(Dreal.equal(new Expression(x), new Expression(y)));
    List<Long> expected = Arrays.asList(x.getHash(), y.getHash());
    for (Variable var : f.getFreeVariables()) {
      assertThat(expected).contains(var.getHash());
    }
  }

  @Test
  public void getVariablesTest() {
    Variable x = new Variable("x");
    Variable y = new Variable("y");
    Expression exp = new Expression(Dreal.add(new Expression(x), new Expression(y)));
    Variables variables = exp.expressionGetVariables();
    for (Variable var : ImmutableList.of(x, y)) {
      assertThat(variables.include(var)).isTrue();
    }
  }

  @Test
  public void getType() {
    Variable x = new Variable("x", Variable.Type.BOOLEAN);
    Variable y = new Variable("y", Variable.Type.INTEGER);
    Variable z = new Variable("z", Variable.Type.CONTINUOUS);
    Variable a = new Variable("a");
    assertThat(x.getType()).isEqualTo(Variable.Type.BOOLEAN);
    assertThat(y.getType()).isEqualTo(Variable.Type.INTEGER);
    assertThat(z.getType()).isEqualTo(Variable.Type.CONTINUOUS);
    assertThat(a.getType()).isEqualTo(Variable.Type.CONTINUOUS);
  }
}
