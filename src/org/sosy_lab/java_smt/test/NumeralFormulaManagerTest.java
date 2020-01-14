/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assert_;

import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

@RunWith(Parameterized.class)
public class NumeralFormulaManagerTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
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

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = Exception.class)
  public void failOnInvalidString() {
    requireIntegers();
    imgr.makeNumber("a");
    assert_().fail();
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void testSubTypes() {
    requireIntegers();
    requireRationals();
    IntegerFormula a = imgr.makeVariable("a");
    RationalFormula r = rmgr.makeVariable("r");
    List<FormulaType<?>> argTypes =
        Lists.newArrayList(FormulaType.RationalType, FormulaType.RationalType);
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
                .isEqualTo(Lists.newArrayList(FormulaType.IntegerType, FormulaType.IntegerType));
          }

          @Override
          protected Void visitDefault(Formula pF) {
            return null;
          }
        });
  }
}
