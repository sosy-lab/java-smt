// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assume;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;

import java.math.BigDecimal;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/** Test for the fix of Issue #457 in Z3. */
public class Z3BigDecimalTest extends SolverBasedTest0 {

  @Before
  public void setupEnvironment() {
    // Only run these tests with Z3 since the issue is Z3-specific
    assume().that(solverToUse()).isEqualTo(Solvers.Z3);
    requireIntegers();
  }

  @Test
  public void testBigDecimalInIntegerFormula() {
    // This would cause a segfault in Z3 before the fix
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(3.5));
    
    // Make sure the number is rounded correctly (truncated to 3)
    IntegerFormula three = imgr.makeNumber(3);
    BooleanFormula equals = bmgr.equal(f, three);
    assertThatFormula(equals).isTautological();
  }

  @Test
  public void testMoreDecimalValues() {
    // Test with more complex values
    IntegerFormula f1 = imgr.makeNumber(BigDecimal.valueOf(2.75));
    IntegerFormula f2 = imgr.makeNumber(BigDecimal.valueOf(-1.333));
    
    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula minusOne = imgr.makeNumber(-1);
    
    BooleanFormula equals1 = bmgr.equal(f1, two);
    BooleanFormula equals2 = bmgr.equal(f2, minusOne);
    
    assertThatFormula(equals1).isTautological();
    assertThatFormula(equals2).isTautological();
  }
  
  @Test
  public void testExactInteger() {
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(42));
    IntegerFormula fortyTwo = imgr.makeNumber(42);
    
    BooleanFormula equals = bmgr.equal(f, fortyTwo);
    assertThatFormula(equals).isTautological();
  }
} 