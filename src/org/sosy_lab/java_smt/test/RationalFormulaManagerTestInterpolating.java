// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.Iterables;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedInterpolatingSolverBasedTest0;

public class RationalFormulaManagerTestInterpolating
    extends ParameterizedInterpolatingSolverBasedTest0 {

  private static final double[] SOME_DOUBLES =
      new double[] {
        0, 0.1, 0.25, 0.5, 1, 1.5, 1.9, 2.1, 2.5, -0.1, -0.5, -1, -1.5, -1.9, -2.1, -2.5,
      };

  @Test
  public void rationalToIntTest() throws SolverException, InterruptedException {
    requireRationals();
    assume()
        .withMessage("Solver %s does not support floor operation", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);

    for (double v : SOME_DOUBLES) {
      IntegerFormula i = imgr.makeNumber((int) Math.floor(v));
      RationalFormula r = rmgr.makeNumber(v);
      assertThat(mgr.getFormulaType(i)).isEqualTo(FormulaType.IntegerType);
      assertThat(mgr.getFormulaType(rmgr.floor(r))).isEqualTo(FormulaType.IntegerType);
      assertThatFormula(imgr.equal(i, rmgr.floor(r))).isSatisfiable();
    }
  }

  @Test
  public void intToIntTest() throws SolverException, InterruptedException {
    requireIntegers();
    for (double v : SOME_DOUBLES) {
      IntegerFormula i = imgr.makeNumber((int) Math.floor(v));
      assertThat(mgr.getFormulaType(i)).isEqualTo(FormulaType.IntegerType);
      assertThat(mgr.getFormulaType(imgr.floor(i))).isEqualTo(FormulaType.IntegerType);
      assertThatFormula(imgr.equal(i, imgr.floor(i))).isTautological();
    }
  }

  @Test
  public void intToIntWithRmgrTest() throws SolverException, InterruptedException {
    requireRationals();
    for (double v : SOME_DOUBLES) {
      IntegerFormula i = imgr.makeNumber((int) Math.floor(v));
      assertThat(mgr.getFormulaType(i)).isEqualTo(FormulaType.IntegerType);
      assertThat(mgr.getFormulaType(imgr.floor(i))).isEqualTo(FormulaType.IntegerType);
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
    assume()
        .withMessage("Solver %s does not support floor operation", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);

    IntegerFormula f = rmgr.floor(rmgr.makeVariable("v"));
    assertThat(mgr.extractVariables(f)).hasSize(1);
    FunctionCollector collector = new FunctionCollector();
    assertThat(mgr.visit(f, collector)).isTrue();
    assertThat(Iterables.getOnlyElement(collector.functions).getKind())
        .isEqualTo(FunctionDeclarationKind.FLOOR);
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

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = Exception.class)
  public void failOnInvalidString() {
    rmgr.makeNumber("a");
    assert_().fail();
  }
}
