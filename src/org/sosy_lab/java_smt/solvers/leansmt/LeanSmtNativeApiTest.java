// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import java.math.BigInteger;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.SolverException;

/** Native API regression tests for LeanSMT. */
public class LeanSmtNativeApiTest {

  private long solver = 0L;

  @BeforeClass
  public static void loadLeanSmt() {
    try {
      LeanSmtNativeApi.loadLibrary(NativeLibraries::loadLibrary);
      LeanSmtNativeApi.initialize();
    } catch (UnsatisfiedLinkError | SolverException e) {
      throw new AssumptionViolatedException("LeanSMT is not available", e);
    }
  }

  @Before
  public void createEnvironment() throws SolverException {
    solver = LeanSmtNativeApi.createSolverCvc5();
    LeanSmtNativeApi.setLogic(solver, "QF_LIA");
  }

  @After
  public void freeEnvironment() throws SolverException {
    LeanSmtNativeApi.deleteSolver(solver);
    solver = 0L;
  }

  private static long declareIntVar(long solver, String name) throws SolverException {
    LeanSmtNativeApi.declareFun(solver, name, "", "Int");
    return LeanSmtNativeApi.mkSymbol(name);
  }

  @Test
  public void simpleSat() throws SolverException {
    long x = declareIntVar(solver, "x");
    long zero = LeanSmtNativeApi.mkIntConst(0L);
    long gt = LeanSmtNativeApi.mkGt(x, zero);
    LeanSmtNativeApi.assertTerm(solver, gt);
    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_SAT);
  }

  @Test
  public void simpleUnsat() throws SolverException {
    long x = declareIntVar(solver, "x");
    long one = LeanSmtNativeApi.mkIntConst(1L);
    long two = LeanSmtNativeApi.mkIntConst(2L);
    LeanSmtNativeApi.assertTerm(solver, LeanSmtNativeApi.mkEq(x, one));
    LeanSmtNativeApi.assertTerm(solver, LeanSmtNativeApi.mkEq(x, two));
    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_UNSAT);
  }

  @Test
  public void bigIntegerEncodingViaFormulaCreator() throws SolverException {
    BigInteger big = new BigInteger("1234567890123456789012345678901234567890");
    LeanSmtFormulaCreator creator = new LeanSmtFormulaCreator();
    LeanSmtNativeApi.declareFun(
        solver, LeanSmtFormulaCreator.encodeNativeIdentifier("x"), "", "Int");
    long x = creator.makeVariable(LeanSmtType.INT, "x");
    long v = creator.makeIntConstant(big);
    long eq =
        creator.makeBinary(
            "=",
            FunctionDeclarationKind.EQ,
            FormulaType.BooleanType,
            x,
            v,
            LeanSmtNativeApi::mkEq);
    LeanSmtNativeApi.assertTermSmtLib(solver, new LeanSmtSmtLibPrinter(creator).dumpTerm(eq));
    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_SAT);
    assertThat(LeanSmtNativeApi.getModel(solver)).contains(big.toString());
  }

  @Test
  public void getValueEvaluatesCompoundTerms() throws SolverException {
    long x = declareIntVar(solver, "x_value");
    long five = LeanSmtNativeApi.mkIntConst(5L);
    long one = LeanSmtNativeApi.mkIntConst(1L);
    long sum = LeanSmtNativeApi.mkAdd(x, one);
    LeanSmtNativeApi.assertTerm(solver, LeanSmtNativeApi.mkEq(x, five));

    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_SAT);
    assertThat(LeanSmtNativeApi.getValue(solver, x)).isEqualTo("5");
    assertThat(LeanSmtNativeApi.getValue(solver, sum)).isEqualTo("6");
  }

  @Test
  public void errorMessageContainsOperationContextForInvalidDelete() {
    SolverException ex = assertThrows(SolverException.class, () -> LeanSmtNativeApi.deleteSolver(0L));
    assertThat(ex).hasMessageThat().contains("deleteSolver");
  }

  @Test
  public void errorMessageContainsOperationContextForInvalidAssert() {
    SolverException ex =
        assertThrows(SolverException.class, () -> LeanSmtNativeApi.assertTerm(solver, 0L));
    assertThat(ex).hasMessageThat().contains("assertTerm");
    assertThat(ex).hasMessageThat().contains("solver=");
    assertThat(ex).hasMessageThat().contains("term=0");
  }

  @Test
  public void bestEffortDeleteDoesNotBlockImmediateRecreate() throws SolverException {
    long extraSolver = LeanSmtNativeApi.createSolverCvc5();
    LeanSmtNativeApi.deleteSolverBestEffort(extraSolver);

    long recreatedSolver = LeanSmtNativeApi.createSolverCvc5();
    try {
      LeanSmtNativeApi.setLogic(recreatedSolver, "QF_LIA");
      long x = declareIntVar(recreatedSolver, "x_recreated");
      long zero = LeanSmtNativeApi.mkIntConst(0L);
      LeanSmtNativeApi.assertTerm(recreatedSolver, LeanSmtNativeApi.mkGe(x, zero));
      assertThat(LeanSmtNativeApi.checkSat(recreatedSolver))
          .isEqualTo(LeanSMTConstants.LEANSMT_SAT);
    } finally {
      LeanSmtNativeApi.deleteSolver(recreatedSolver);
    }
  }

}
