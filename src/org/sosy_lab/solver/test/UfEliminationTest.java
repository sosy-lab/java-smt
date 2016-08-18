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
package org.sosy_lab.solver.test;

import static com.google.common.collect.Lists.newArrayList;
import static org.junit.Assert.fail;
import static org.sosy_lab.solver.api.FormulaType.BooleanType;
import static org.sosy_lab.solver.api.FormulaType.IntegerType;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Lists;
import com.google.common.truth.Truth;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.basicimpl.tactics.UfElimination;
import org.sosy_lab.solver.basicimpl.tactics.UfElimination.Result;

import java.util.Map;

@RunWith(Parameterized.class)
public class UfEliminationTest extends SolverBasedTest0 {

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

  private UfElimination ackermannization;

  @Before
  public void setUp() throws Exception {
    ackermannization = new UfElimination(mgr);
  }

  @Test
  public void simpleTest() throws SolverException, InterruptedException {
    // f := uf(v1, v3) XOR uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable1, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable2, variable4));
    BooleanFormula f = bmgr.xor(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4);

    BooleanFormula withOutUfs = ackermannization.eliminateUfs(f);
    assertThatFormula(f).isSatisfiable(); // sanity check
    assertThatFormula(withOutUfs).isSatisfiable();
    assertThatFormula(bmgr.and(argsEqual, f)).isUnsatisfiable(); // sanity check
    assertThatFormula(bmgr.and(argsEqual, withOutUfs)).isUnsatisfiable();

    // check that UFs were really eliminated
    Map<String, Formula> variablesAndUFs = mgr.extractVariablesAndUFs(withOutUfs);
    Map<String, Formula> variables = mgr.extractVariables(withOutUfs);
    Truth.assertThat(variablesAndUFs).doesNotContainKey("uf");
    Truth.assertThat(variablesAndUFs).isEqualTo(variables);
  }

  @Test
  public void nestedUfs() throws SolverException, InterruptedException {
    // f := uf2(uf1(v1, v2), v3) XOR uf2(uf1(v2, v1), v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<IntegerFormula> uf1Decl =
        fmgr.declareUF("uf1", IntegerType, Lists.newArrayList(IntegerType, IntegerType));
    Formula uf1a = fmgr.callUF(uf1Decl, variable1, variable2);
    Formula uf1b = fmgr.callUF(uf1Decl, variable2, variable1);
    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf2", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(uf1a, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(uf1b, variable4));
    BooleanFormula f = bmgr.xor(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4);

    BooleanFormula withOutUfs = ackermannization.eliminateUfs(f);
    assertThatFormula(f).isSatisfiable(); // sanity check
    assertThatFormula(withOutUfs).isSatisfiable();
    assertThatFormula(bmgr.and(argsEqual, f)).isUnsatisfiable(); // sanity check
    assertThatFormula(bmgr.and(argsEqual, withOutUfs)).isUnsatisfiable();

    // check that UFs were really eliminated
    Map<String, Formula> variablesAndUFs = mgr.extractVariablesAndUFs(withOutUfs);
    Map<String, Formula> variables = mgr.extractVariables(withOutUfs);
    Truth.assertThat(variablesAndUFs).doesNotContainKey("uf1");
    Truth.assertThat(variablesAndUFs).doesNotContainKey("uf2");
    Truth.assertThat(variablesAndUFs).isEqualTo(variables);
  }

  @Test
  public void nestedUfs2() throws SolverException, InterruptedException {
    // f := uf2(uf1(v1, uf2(v3, v6)), v3) < uf2(uf1(v2, uf2(v4, v5)), v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    IntegerFormula variable5 = imgr.makeVariable("variable5");
    IntegerFormula variable6 = imgr.makeVariable("variable6");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);
    BooleanFormula v5EqualsV6 = imgr.equal(variable5, variable6);

    FunctionDeclaration<IntegerFormula> uf1Decl =
        fmgr.declareUF("uf1", IntegerType, Lists.newArrayList(IntegerType, IntegerType));
    FunctionDeclaration<IntegerFormula> uf2Decl =
        fmgr.declareUF("uf2", IntegerType, Lists.newArrayList(IntegerType, IntegerType));
    Formula uf2a = fmgr.callUF(uf2Decl, variable1, variable2);
    Formula uf2b = fmgr.callUF(uf2Decl, variable1, variable2);

    Formula uf1a = fmgr.callUF(uf1Decl, variable1, uf2a);
    Formula uf1b = fmgr.callUF(uf1Decl, variable2, uf2b);

    IntegerFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(uf1a, variable3));
    IntegerFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(uf1b, variable4));
    BooleanFormula f = imgr.lessThan(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4, v5EqualsV6);

    BooleanFormula withOutUfs = ackermannization.eliminateUfs(f);
    assertThatFormula(f).isSatisfiable(); // sanity check
    assertThatFormula(withOutUfs).isSatisfiable();
    assertThatFormula(bmgr.and(argsEqual, f)).isUnsatisfiable(); // sanity check
    assertThatFormula(bmgr.and(argsEqual, withOutUfs)).isUnsatisfiable();

    // check that UFs were really eliminated
    Map<String, Formula> variablesAndUFs = mgr.extractVariablesAndUFs(withOutUfs);
    Map<String, Formula> variables = mgr.extractVariables(withOutUfs);
    Truth.assertThat(variablesAndUFs).doesNotContainKey("uf1");
    Truth.assertThat(variablesAndUFs).doesNotContainKey("uf2");
    Truth.assertThat(variablesAndUFs).isEqualTo(variables);
  }

  @Test
  public void twoFormulasTest() throws SolverException, InterruptedException {
    // See FormulaManagerTest.testEmptySubstitution(), FormulaManagerTest.testNoSubstitution()
    if (solverToUse().equals(Solvers.PRINCESS)) {
      requireFalse(Solvers.PRINCESS + " fails.");
    }

    // f := uf(v1, v3) XOR uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable1, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable2, variable4));
    BooleanFormula f = bmgr.xor(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4);

    Result result1 = ackermannization.eliminateUfs(f1, Result.empty(mgr));
    BooleanFormula withOutUfs1 = result1.getFormula();
    Result result2 = ackermannization.eliminateUfs(f2, result1);
    BooleanFormula withOutUfs2 = result2.getFormula();
    BooleanFormula geConstraints = result2.geConstraints();
    BooleanFormula withOutUfs = bmgr.and(bmgr.xor(withOutUfs1, withOutUfs2), geConstraints);
    assertThatFormula(f).isSatisfiable(); // sanity check
    assertThatFormula(withOutUfs).isSatisfiable();
    assertThatFormula(bmgr.and(argsEqual, f)).isUnsatisfiable(); // sanity check
    assertThatFormula(bmgr.and(argsEqual, withOutUfs)).isUnsatisfiable();

    // check that UFs were really eliminated
    Map<String, Formula> variablesAndUFs = mgr.extractVariablesAndUFs(withOutUfs);
    Map<String, Formula> variables = mgr.extractVariables(withOutUfs);
    Truth.assertThat(variablesAndUFs).doesNotContainKey("uf");
    Truth.assertThat(variablesAndUFs).isEqualTo(variables);
  }

  @Test
  public void quantifierTest() {
    requireQuantifiers();
    // f := exists v1,v2v,v3,v4 : uf(v1, v3) == uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable1, variable3));
    BooleanFormula f2 = fmgr.callUF(uf2Decl, Lists.newArrayList(variable2, variable4));
    BooleanFormula f =
        qmgr.exists(
            newArrayList(variable1, variable2, variable3, variable4), bmgr.equivalence(f1, f2));

    try {
      ackermannization.eliminateUfs(f);
      fail();
    } catch (IllegalArgumentException expected) {
    }
  }

  @Test
  public void substitutionTest() throws SolverException, InterruptedException {
    // f := uf(v1, v3) \/ NOT(uf(v2, v4)))
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> ufDecl =
        fmgr.declareUF("uf", BooleanType, Lists.newArrayList(IntegerType, IntegerType));
    BooleanFormula f1 = fmgr.callUF(ufDecl, Lists.newArrayList(variable1, variable3));
    BooleanFormula f2 = fmgr.callUF(ufDecl, Lists.newArrayList(variable2, variable4));
    BooleanFormula f = bmgr.or(f1, bmgr.not(f2));

    Result withOutUfs = ackermannization.eliminateUfs(f, Result.empty(mgr));

    Map<Formula, Formula> substitution = withOutUfs.getSubstitution();
    Truth.assertThat(substitution).hasSize(2);

    BiMap<Formula, Formula> inverseSubstitution = HashBiMap.create(substitution).inverse();
    BooleanFormula revertedSubstitution =
        mgr.substitute(withOutUfs.getFormula(), inverseSubstitution);
    assertThatFormula(f).isEquivalentTo(revertedSubstitution);
  }
}
