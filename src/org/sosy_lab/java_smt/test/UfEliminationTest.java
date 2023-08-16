// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.api.FormulaType.BooleanType;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;
import java.util.Map;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.utils.SolverUtils;
import org.sosy_lab.java_smt.utils.UfElimination;
import org.sosy_lab.java_smt.utils.UfElimination.Result;

public class UfEliminationTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private UfElimination ackermannization;

  @Before
  public void setUp() {
    ackermannization = SolverUtils.ufElimination(mgr);
    requireUF();
  }

  @Test
  public void simpleTest() throws SolverException, InterruptedException {
    requireIntegers();

    // f := uf(v1, v3) XOR uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(uf2Decl, variable1, variable3);
    BooleanFormula f2 = fmgr.callUF(uf2Decl, variable2, variable4);
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
    requireIntegers();

    // f := uf2(uf1(v1, v2), v3) XOR uf2(uf1(v2, v1), v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<IntegerFormula> uf1Decl =
        fmgr.declareUF("uf1", IntegerType, IntegerType, IntegerType);
    Formula uf1a = fmgr.callUF(uf1Decl, variable1, variable2);
    Formula uf1b = fmgr.callUF(uf1Decl, variable2, variable1);
    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf2", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(uf2Decl, uf1a, variable3);
    BooleanFormula f2 = fmgr.callUF(uf2Decl, uf1b, variable4);
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
    requireIntegers();

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
        fmgr.declareUF("uf1", IntegerType, IntegerType, IntegerType);
    FunctionDeclaration<IntegerFormula> uf2Decl =
        fmgr.declareUF("uf2", IntegerType, IntegerType, IntegerType);
    Formula uf2a = fmgr.callUF(uf2Decl, variable1, variable2);
    Formula uf2b = fmgr.callUF(uf2Decl, variable1, variable2);

    Formula uf1a = fmgr.callUF(uf1Decl, variable1, uf2a);
    Formula uf1b = fmgr.callUF(uf1Decl, variable2, uf2b);

    IntegerFormula f1 = fmgr.callUF(uf2Decl, uf1a, variable3);
    IntegerFormula f2 = fmgr.callUF(uf2Decl, uf1b, variable4);
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
  public void nestedUfs3() throws SolverException, InterruptedException {
    requireIntegers();

    // f := uf(v1) < uf(v2)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");

    FunctionDeclaration<IntegerFormula> ufDecl = fmgr.declareUF("uf", IntegerType, IntegerType);
    IntegerFormula f1 = fmgr.callUF(ufDecl, variable1);
    IntegerFormula f2 = fmgr.callUF(ufDecl, variable2);
    BooleanFormula f = imgr.lessThan(f1, f2);
    BooleanFormula argsEqual = imgr.equal(variable1, variable2);

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
    requireIntegers();
    assume().withMessage("Princess fails").that(solver).isNotEqualTo(Solvers.PRINCESS);

    // f := uf(v1, v3) XOR uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");
    BooleanFormula v1EqualsV2 = imgr.equal(variable1, variable2);
    BooleanFormula v3EqualsV4 = imgr.equal(variable3, variable4);

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(uf2Decl, variable1, variable3);
    BooleanFormula f2 = fmgr.callUF(uf2Decl, variable2, variable4);
    BooleanFormula f = bmgr.xor(f1, f2);
    BooleanFormula argsEqual = bmgr.and(v1EqualsV2, v3EqualsV4);

    Result result1 = ackermannization.eliminateUfs(f1, Result.empty(mgr));
    BooleanFormula withOutUfs1 = result1.getFormula();
    Result result2 = ackermannization.eliminateUfs(f2, result1);
    BooleanFormula withOutUfs2 = result2.getFormula();
    BooleanFormula geConstraints = result2.getConstraints();
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
    requireIntegers();

    // f := exists v1,v2v,v3,v4 : uf(v1, v3) == uf(v2, v4)
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(uf2Decl, variable1, variable3);
    BooleanFormula f2 = fmgr.callUF(uf2Decl, variable2, variable4);
    BooleanFormula f =
        qmgr.exists(
            ImmutableList.of(variable1, variable2, variable3, variable4), bmgr.equivalence(f1, f2));

    try {
      ackermannization.eliminateUfs(f);
      assert_().fail();
    } catch (IllegalArgumentException expected) {
    }
  }

  @Test
  public void substitutionTest() throws SolverException, InterruptedException {
    requireIntegers();

    // f := uf(v1, v3) \/ NOT(uf(v2, v4)))
    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> ufDecl =
        fmgr.declareUF("uf", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(ufDecl, variable1, variable3);
    BooleanFormula f2 = fmgr.callUF(ufDecl, variable2, variable4);
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
