// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import java.math.BigDecimal;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Test for the fix of Issue #457 in Z3. The issue was a segfault when calling
 * IntegerFormulaManager.makeNumber with BigDecimal values that have fractional parts.
 */
public class Z3BigDecimalTest extends SolverBasedTest0 {

  @Before
  public void setupEnvironment() {
    requireSolver(Solvers.Z3);
    requireIntegers();
  }

  @Test
  public void testBigDecimalInIntegerFormula() throws SolverException, InterruptedException {
    // This would cause a segfault in Z3 before the fix
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(3.5));
    
    // Make sure the number is truncated correctly to 3
    IntegerFormula three = imgr.makeNumber(3);
    BooleanFormula equals = bmgr.equal(f, three);
    
    // Verify the formula evaluates correctly
    assertThatFormula(equals).isSatisfiable();
    
    // Double-check using model evaluation
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(bmgr.not(equals));
      assertThat(prover.isUnsat()).isTrue();
    }
  }

  @Test
  public void testMoreDecimalValues() throws SolverException, InterruptedException {
    // Test with more complex values
    IntegerFormula f1 = imgr.makeNumber(BigDecimal.valueOf(2.75));
    IntegerFormula f2 = imgr.makeNumber(BigDecimal.valueOf(-1.333));
    
    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula minusOne = imgr.makeNumber(-1);
    
    assertThatFormula(bmgr.equal(f1, two)).isSatisfiable();
    assertThatFormula(bmgr.equal(f2, minusOne)).isSatisfiable();
  }
  
  @Test
  public void testExactInteger() throws SolverException, InterruptedException {
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(42));
    IntegerFormula fortyTwo = imgr.makeNumber(42);
    
    assertThatFormula(bmgr.equal(f, fortyTwo)).isSatisfiable();
  }
  
  @Test
  public void testZero() throws SolverException, InterruptedException {
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(0.1));
    IntegerFormula zero = imgr.makeNumber(0);
    
    assertThatFormula(bmgr.equal(f, zero)).isSatisfiable();
  }
  
  @Test
  public void testNegativeZero() throws SolverException, InterruptedException {
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(-0.1));
    IntegerFormula zero = imgr.makeNumber(0);
    
    assertThatFormula(bmgr.equal(f, zero)).isSatisfiable();
  }
  
  @Test
  public void testLargeDecimals() throws SolverException, InterruptedException {
    IntegerFormula f = imgr.makeNumber(
        BigDecimal.valueOf(Long.MAX_VALUE).add(BigDecimal.valueOf(0.99)));
    IntegerFormula expected = imgr.makeNumber(BigDecimal.valueOf(Long.MAX_VALUE).toBigInteger());
    
    assertThatFormula(bmgr.equal(f, expected)).isSatisfiable();
  }
} 