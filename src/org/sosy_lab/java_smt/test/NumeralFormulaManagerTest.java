// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
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
