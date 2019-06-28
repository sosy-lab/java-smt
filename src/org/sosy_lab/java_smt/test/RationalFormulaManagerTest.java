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
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.common.collect.Iterables;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

@RunWith(Parameterized.class)
public class RationalFormulaManagerTest extends SolverBasedTest0 {

  private static final double[] SOME_DOUBLES =
      new double[] {
        0, 0.1, 0.25, 0.5, 1, 1.5, 1.9, 2.1, 2.5, -0.1, -0.5, -1, -1.5, -1.9, -2.1, -2.5,
      };

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
  public void rationalToIntTest() throws SolverException, InterruptedException {
    requireRationals();
    for (double v : SOME_DOUBLES) {
      IntegerFormula i = imgr.makeNumber((int) Math.floor(v));
      RationalFormula r = rmgr.makeNumber(v);
      assertEquals(mgr.getFormulaType(i), FormulaType.IntegerType);
      assertEquals(mgr.getFormulaType(rmgr.floor(r)), FormulaType.IntegerType);
      assertThatFormula(imgr.equal(i, rmgr.floor(r))).isSatisfiable();
    }
  }

  @Test
  public void intToIntTest() throws SolverException, InterruptedException {
    for (double v : SOME_DOUBLES) {
      IntegerFormula i = imgr.makeNumber((int) Math.floor(v));
      assertEquals(mgr.getFormulaType(i), FormulaType.IntegerType);
      assertEquals(mgr.getFormulaType(imgr.floor(i)), FormulaType.IntegerType);
      assertThatFormula(imgr.equal(i, imgr.floor(i))).isTautological();
    }
  }

  @Test
  public void intToIntWithRmgrTest() throws SolverException, InterruptedException {
    requireRationals();
    for (double v : SOME_DOUBLES) {
      IntegerFormula i = imgr.makeNumber((int) Math.floor(v));
      assertEquals(mgr.getFormulaType(i), FormulaType.IntegerType);
      assertEquals(mgr.getFormulaType(rmgr.floor(i)), FormulaType.IntegerType);
      assertThatFormula(imgr.equal(i, rmgr.floor(i))).isTautological();
    }
  }

  @Test
  public void floorIsLessOrEqualsValueTest() throws SolverException, InterruptedException {
    requireRationals();
    requireQuantifiers();
    RationalFormula v = rmgr.makeVariable("v");
    assertThatFormula(rmgr.lessOrEquals(rmgr.floor(v), v)).isTautological();
  }

  @Test
  public void floorIsGreaterThanValueTest() throws SolverException, InterruptedException {
    requireRationals();
    requireQuantifiers();
    RationalFormula v = rmgr.makeVariable("v");
    assertThatFormula(rmgr.lessOrEquals(rmgr.floor(v), v)).isTautological();
  }

  @Test
  public void forallFloorIsLessOrEqualsValueTest() throws SolverException, InterruptedException {
    requireRationals();
    requireQuantifiers();
    RationalFormula v = rmgr.makeVariable("v");
    assertThatFormula(qmgr.forall(v, rmgr.lessOrEquals(rmgr.floor(v), v))).isTautological();
  }

  @Test
  public void forallFloorIsLessThanValueTest() throws SolverException, InterruptedException {
    requireRationals();
    requireQuantifiers();
    RationalFormula v = rmgr.makeVariable("v");
    // counterexample: all integers
    assertThatFormula(qmgr.forall(v, rmgr.lessThan(rmgr.floor(v), v))).isUnsatisfiable();
  }

  @Test
  public void visitFloorTest() {
    requireRationals();
    IntegerFormula f = rmgr.floor(rmgr.makeVariable("v"));
    assertThat(mgr.extractVariables(f)).hasSize(1);
    FunctionCollector collector = new FunctionCollector();
    assertTrue(mgr.visit(f, collector));
    assertEquals(
        FunctionDeclarationKind.FLOOR, Iterables.getOnlyElement(collector.functions).getKind());
  }

  private static final class FunctionCollector extends DefaultFormulaVisitor<Boolean> {

    private final Set<FunctionDeclaration<?>> functions = new HashSet<>();

    @Override
    public Boolean visitFunction(
        Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
      functions.add(pFunctionDeclaration);
      return true;
    }

    @Override
    protected Boolean visitDefault(Formula pF) {
      return true;
    }
  }

  @Test(expected = Exception.class)
  public void failOnInvalidString() {
    rmgr.makeNumber("a");
    fail();
  }
}
