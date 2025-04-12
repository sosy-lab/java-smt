// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

public class NumeralFormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void divZeroTest() throws SolverException, InterruptedException {
    requireIntegers();
    assume().that(solver).isNoneOf(Solvers.OPENSMT, Solvers.YICES2); // No division by zero

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula three = imgr.makeNumber(3);
    IntegerFormula seven = imgr.makeNumber(7);

    // Show that 3/0=0 and 3/0=7 can hold separately
    IntegerFormula f1 = imgr.divide(three, zero);
    assertThatFormula(imgr.equal(f1, zero)).isSatisfiable();
    assertThatFormula(imgr.equal(f1, seven)).isSatisfiable();

    // But if 3/0=0 in the model, it can't also be another value
    IntegerFormula var = imgr.makeVariable("var");
    IntegerFormula f2 = imgr.divide(var, zero);
    IntegerFormula res = imgr.makeVariable("res");
    assertThatFormula(
            bmgr.and(
                imgr.equal(f1, zero),
                imgr.equal(var, three),
                imgr.equal(f2, res),
                bmgr.not(imgr.equal(res, zero))))
        .isUnsatisfiable();

    // Show that a=b => a/0=b/0
    IntegerFormula var1 = imgr.makeVariable("arg1");
    IntegerFormula var2 = imgr.makeVariable("arg2");
    assertThatFormula(
            bmgr.implication(
                imgr.equal(var1, var2),
                imgr.equal(imgr.divide(var1, zero), imgr.divide(var2, zero))))
        .isTautological();
  }

  @Test
  public void modZeroTest() throws SolverException, InterruptedException {
    requireIntegers();
    assume().that(solver).isNoneOf(Solvers.OPENSMT, Solvers.YICES2); // No division by zero

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula three = imgr.makeNumber(3);
    IntegerFormula seven = imgr.makeNumber(7);

    // Show that 3%0=0 and 3%0=7 can hold separately
    IntegerFormula f1 = imgr.modulo(three, zero);
    assertThatFormula(imgr.equal(f1, zero)).isSatisfiable();
    assertThatFormula(imgr.equal(f1, seven)).isSatisfiable();

    // But if 3%0=0 in the model, it can't also be another value
    IntegerFormula var = imgr.makeVariable("var");
    IntegerFormula f2 = imgr.modulo(var, zero);
    IntegerFormula res = imgr.makeVariable("res");
    assertThatFormula(
            bmgr.and(
                imgr.equal(f1, zero),
                imgr.equal(var, three),
                imgr.equal(f2, res),
                bmgr.not(imgr.equal(res, zero))))
        .isUnsatisfiable();

    // Show that a=b => a%0=b%0
    IntegerFormula var1 = imgr.makeVariable("arg1");
    IntegerFormula var2 = imgr.makeVariable("arg2");
    assertThatFormula(
            bmgr.implication(
                imgr.equal(var1, var2),
                imgr.equal(imgr.modulo(var1, zero), imgr.modulo(var2, zero))))
        .isTautological();
  }

  @Test
  public void distinctTest() throws SolverException, InterruptedException {
    requireIntegers();
    List<IntegerFormula> symbols = new ArrayList<>();
    for (int i = 0; i < 5; i++) {
      IntegerFormula symbol = imgr.makeVariable("x" + i);
      symbols.add(symbol);
    }
    assertThatFormula(imgr.distinct(symbols)).isSatisfiable();
  }

  @Test
  public void distinctTest2() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula four = imgr.makeNumber(4);
    List<IntegerFormula> symbols = new ArrayList<>();
    List<BooleanFormula> constraints = new ArrayList<>();
    for (int i = 0; i < 5; i++) {
      IntegerFormula symbol = imgr.makeVariable("x" + i);
      symbols.add(symbol);
      constraints.add(imgr.lessOrEquals(zero, symbol));
      constraints.add(imgr.lessOrEquals(symbol, four));
    }
    assertThatFormula(bmgr.and(imgr.distinct(symbols), bmgr.and(constraints))).isSatisfiable();
  }

  @Test
  public void distinctTest3() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula four = imgr.makeNumber(4);
    List<IntegerFormula> symbols = new ArrayList<>();
    List<BooleanFormula> constraints = new ArrayList<>();
    for (int i = 0; i < 5; i++) {
      IntegerFormula symbol = imgr.makeVariable("x" + i);
      symbols.add(symbol);
      constraints.add(imgr.lessOrEquals(zero, symbol));
      constraints.add(imgr.lessThan(symbol, four));
    }
    assertThatFormula(bmgr.and(imgr.distinct(symbols), bmgr.and(constraints))).isUnsatisfiable();
  }

  @Test
  public void trivialDistinctTest() throws SolverException, InterruptedException {
    requireIntegers();
    assertThatFormula(imgr.distinct(ImmutableList.of())).isTautological();
    assertThatFormula(imgr.distinct(ImmutableList.of(imgr.makeVariable("a")))).isTautological();
  }

  @Test
  public void trivialSumTest() throws SolverException, InterruptedException {
    requireIntegers();
    assertThatFormula(imgr.equal(imgr.sum(ImmutableList.of()), imgr.makeNumber(0)))
        .isTautological();
    assertThatFormula(
            imgr.equal(imgr.sum(ImmutableList.of(imgr.makeVariable("a"))), imgr.makeVariable("a")))
        .isTautological();
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void failOnInvalidStringInteger() {
    requireIntegers();
    assertThrows(Exception.class, () -> imgr.makeNumber("a"));
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void failOnInvalidStringRational() {
    requireIntegers();
    assertThrows(Exception.class, () -> rmgr.makeNumber("a"));
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void testSubTypes() {
    requireIntegers();
    requireRationals();
    IntegerFormula a = imgr.makeVariable("a");
    RationalFormula r = rmgr.makeVariable("r");
    List<FormulaType<?>> argTypes =
        ImmutableList.of(FormulaType.RationalType, FormulaType.RationalType);
    FunctionDeclaration<IntegerFormula> ufDecl =
        fmgr.declareUF("uf", FormulaType.IntegerType, argTypes);
    IntegerFormula uf = fmgr.callUF(ufDecl, a, r);

    mgr.visit(
        bmgr.and(rmgr.equal(uf, imgr.makeNumber(0))),
        new DefaultFormulaVisitor<Void>() {

          @Override
          public Void visitFunction(
              Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pDeclaration) {
            if ("uf".equals(pDeclaration.getName())) {
              checkUf(pDeclaration);
            } else {
              checkIntEq(pDeclaration);
            }
            return null;
          }

          private void checkUf(FunctionDeclaration<?> pDeclaration) {
            assertThat(pDeclaration.getArgumentTypes()).isEqualTo(argTypes);
            FunctionDeclaration<?> ufDecl2 =
                fmgr.declareUF("uf", pDeclaration.getType(), pDeclaration.getArgumentTypes());
            Formula uf2 = fmgr.callUF(ufDecl2, a, r);
            assertThat(uf2).isEqualTo(uf);
            fmgr.callUF(ufDecl2, r, r);
          }

          private void checkIntEq(FunctionDeclaration<?> pDeclaration) {
            assertThat(pDeclaration.getArgumentTypes())
                .containsExactly(FormulaType.IntegerType, FormulaType.IntegerType)
                .inOrder();
          }

          @Override
          protected Void visitDefault(Formula pF) {
            return null;
          }
        });
  }
}
