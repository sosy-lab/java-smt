/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.test.SolverVisitorTest.FunctionDeclarationVisitorNoOther;

public class RotationVisitorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private BitvectorFormula a;
  private BitvectorFormula y;

  @Before
  public void init() {
    requireBitvectors();
    requireVisitor();

    a = bvmgr.makeVariable(8, "a");
    y = bvmgr.makeBitvector(8, 1);
  }

  @Test
  public void rotateLeftTest() {
    BitvectorFormula f = bvmgr.rotateLeft(a, y);

    var variables = mgr.extractVariablesAndUFs(f);
    assertThat(variables).hasSize(1);
    assertThat(variables).containsKey("a");

    var functions = mgr.visit(f, new FunctionDeclarationVisitorNoOther(mgr));
    switch (solverToUse()) {
      case CVC4:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_OR,
                FunctionDeclarationKind.BV_SHL,
                FunctionDeclarationKind.ITE,
                FunctionDeclarationKind.ITE,
                FunctionDeclarationKind.EQ,
                FunctionDeclarationKind.EQ,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_LSHR,
                FunctionDeclarationKind.BV_SUB);
        break;
      case CVC5:
      case PRINCESS:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_OR,
                FunctionDeclarationKind.BV_SHL,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_LSHR,
                FunctionDeclarationKind.BV_SUB);
        break;
      case MATHSAT5:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_OR,
                FunctionDeclarationKind.BV_LSHR,
                FunctionDeclarationKind.BV_SHL);
        break;
      case YICES2:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_CONCAT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT);
        break;
      default:
        assertThat(functions).containsExactly(FunctionDeclarationKind.BV_ROTATE_LEFT);
    }

    // TODO dumpFormula crashes with Princess
    // System.out.println(mgr.dumpFormula(bvmgr.equal(a, f)));
  }

  @Test
  public void rotateRightTest() {
    BitvectorFormula f = bvmgr.rotateRight(a, y);

    var variables = mgr.extractVariablesAndUFs(f);
    assertThat(variables).hasSize(1);
    assertThat(variables).containsKey("a");

    var functions = mgr.visit(f, new FunctionDeclarationVisitorNoOther(mgr));
    switch (solverToUse()) {
      case CVC4:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_OR,
                FunctionDeclarationKind.BV_LSHR,
                FunctionDeclarationKind.ITE,
                FunctionDeclarationKind.ITE,
                FunctionDeclarationKind.EQ,
                FunctionDeclarationKind.EQ,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_SHL,
                FunctionDeclarationKind.BV_SUB);
        break;
      case CVC5:
      case PRINCESS:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_OR,
                FunctionDeclarationKind.BV_SHL,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_SMOD,
                FunctionDeclarationKind.BV_LSHR,
                FunctionDeclarationKind.BV_SUB);
        break;
      case MATHSAT5:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_OR,
                FunctionDeclarationKind.BV_LSHR,
                FunctionDeclarationKind.BV_SHL);
        break;
      case YICES2:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_CONCAT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT);
        break;
      default:
        assertThat(functions).containsExactly(FunctionDeclarationKind.BV_ROTATE_RIGHT);
    }
  }

  @Test
  public void rotateLeftIntegerTest() {
    BitvectorFormula f = bvmgr.rotateLeft(a, 1);

    var variables = mgr.extractVariablesAndUFs(f);
    assertThat(variables).hasSize(1);
    assertThat(variables).containsKey("a");

    var functions = mgr.visit(f, new FunctionDeclarationVisitorNoOther(mgr));
    switch (solverToUse()) {
      case PRINCESS:
        assertThat(functions)
            .containsExactly(FunctionDeclarationKind.BV_EXTRACT, FunctionDeclarationKind.BV_CONCAT);
        break;
      case YICES2:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_CONCAT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT);
        break;
      default:
        assertThat(functions).containsExactly(FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT);
    }
  }

  @Test
  public void rotateRightIntegerTest() {
    BitvectorFormula f = bvmgr.rotateRight(a, 1);

    var variables = mgr.extractVariablesAndUFs(f);
    assertThat(variables).hasSize(1);
    assertThat(variables).containsKey("a");

    var functions = mgr.visit(f, new FunctionDeclarationVisitorNoOther(mgr));
    switch (solverToUse()) {
      case PRINCESS:
        assertThat(functions)
            .containsExactly(FunctionDeclarationKind.BV_EXTRACT, FunctionDeclarationKind.BV_CONCAT);
        break;
      case YICES2:
        assertThat(functions)
            .containsExactly(
                FunctionDeclarationKind.BV_CONCAT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT,
                FunctionDeclarationKind.BV_EXTRACT);
        break;
      default:
        assertThat(functions).containsExactly(FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT);
    }
  }
}
