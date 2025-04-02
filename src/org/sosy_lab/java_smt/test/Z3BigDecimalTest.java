// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;

import java.math.BigDecimal;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/** Test for the fix of Issue #457 in Z3. */
@RunWith(Parameterized.class)
public class Z3BigDecimalTest extends SolverBasedTest0 {

  @Parameterized.Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Before
  public void setupEnvironment() {
    requireIntegers();
  }

  @Test
  public void testBigDecimalInIntegerFormula() {
    // This would cause a segfault in Z3 before the fix
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(3.5));
    
    // Make sure the number is rounded correctly (truncated to 3)
    IntegerFormula three = imgr.makeNumber(3);
    assertThat(mgr.getBooleanFormulaManager().equals(f, three)).isTrue();
  }

  @Test
  public void testMoreDecimalValues() {
    // Test with more complex values
    IntegerFormula f1 = imgr.makeNumber(BigDecimal.valueOf(2.75));
    IntegerFormula f2 = imgr.makeNumber(BigDecimal.valueOf(-1.333));
    
    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula minusOne = imgr.makeNumber(-1);
    
    assertThat(mgr.getBooleanFormulaManager().equals(f1, two)).isTrue();
    assertThat(mgr.getBooleanFormulaManager().equals(f2, minusOne)).isTrue();
  }
  
  @Test
  public void testExactInteger() {
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(42));
    IntegerFormula fortyTwo = imgr.makeNumber(42);
    
    assertThat(mgr.getBooleanFormulaManager().equals(f, fortyTwo)).isTrue();
  }
} 