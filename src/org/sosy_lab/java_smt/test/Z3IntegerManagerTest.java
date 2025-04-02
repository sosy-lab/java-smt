// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.junit.Assume.assumeTrue;

import java.math.BigDecimal;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/**
 * Simple test to verify Z3 doesn't segfault with BigDecimal values.
 * Tests the fix for issue #457.
 */
public class Z3IntegerManagerTest extends SolverBasedTest0 {

  @Before
  public void setupTest() {
    assumeTrue(solverToUse() == Solvers.Z3);
    requireIntegers();
  }

  @Test
  public void testZ3WithBigDecimal() {
    // This would cause a segfault before the fix
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(3.5));
    
    // Just testing that we get here without a segfault
    // No assertions needed - if Z3 segfaults, the test will fail automatically
  }
} 