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

  @Test
  public void simpleSat() throws SolverException {
    long x = LeanSmtNativeApi.mkIntVar(solver, "x");
    long zero = LeanSmtNativeApi.mkIntConst(0L);
    long gt = LeanSmtNativeApi.mkGt(x, zero);
    LeanSmtNativeApi.assertTerm(solver, gt);
    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_SAT);
  }

  @Test
  public void simpleUnsat() throws SolverException {
    long x = LeanSmtNativeApi.mkIntVar(solver, "x");
    long one = LeanSmtNativeApi.mkIntConst(1L);
    long two = LeanSmtNativeApi.mkIntConst(2L);
    LeanSmtNativeApi.assertTerm(solver, LeanSmtNativeApi.mkEq(x, one));
    LeanSmtNativeApi.assertTerm(solver, LeanSmtNativeApi.mkEq(x, two));
    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_UNSAT);
  }

  @Test
  public void bigIntegerEncodingViaFormulaCreator() throws SolverException {
    BigInteger big = new BigInteger("1234567890123456789012345678901234567890");
    LeanSmtFormulaCreator creator = new LeanSmtFormulaCreator(solver);
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
    LeanSmtNativeApi.assertTerm(solver, eq);
    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_SAT);
    assertThat(LeanSmtNativeApi.getModel(solver)).contains(big.toString());
  }

  @Test
  public void getValueEvaluatesCompoundTerms() throws SolverException {
    long x = LeanSmtNativeApi.mkIntVar(solver, "x_value");
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
  public void parserAcceptsQuotedCoreOperators() throws SolverException {
    LeanSmtFormulaCreator creator = new LeanSmtFormulaCreator(solver);
    long formula =
        new LeanSmtParser(creator).parse("(assert (|and| true (|xor| false true)))");

    LeanSmtNativeApi.assertTerm(solver, formula);

    assertThat(LeanSmtNativeApi.checkSat(solver)).isEqualTo(LeanSMTConstants.LEANSMT_SAT);
  }
}
