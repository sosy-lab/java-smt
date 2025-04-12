// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;

public class IntegerFormulaManagerTest extends ParameterizedSolverBasedTest0 {

  @Before
  public void init() {
    requireIntegers();
  }

  private void checkEqualInt(BigDecimal bd, BigInteger bi)
      throws SolverException, InterruptedException {
    assertThatFormula(imgr.equal(imgr.makeNumber(bd), imgr.makeNumber(bi))).isTautological();
  }

  @Test
  public void testIntegers() throws SolverException, InterruptedException {
    checkEqualInt(BigDecimal.valueOf(0), BigInteger.valueOf(0));
    checkEqualInt(BigDecimal.valueOf(4), BigInteger.valueOf(4));
    checkEqualInt(BigDecimal.valueOf(4.01), BigInteger.valueOf(4));
    checkEqualInt(BigDecimal.valueOf(4.5), BigInteger.valueOf(4));
    checkEqualInt(BigDecimal.valueOf(4.99), BigInteger.valueOf(4));
    checkEqualInt(BigDecimal.valueOf(-4), BigInteger.valueOf(-4));
    checkEqualInt(BigDecimal.valueOf(-3.01), BigInteger.valueOf(-4));
    checkEqualInt(BigDecimal.valueOf(-3.5), BigInteger.valueOf(-4));
    checkEqualInt(BigDecimal.valueOf(-3.99), BigInteger.valueOf(-4));
    checkEqualInt(
        new BigDecimal("12345678901234567890.123"), new BigInteger("12345678901234567890"));
    checkEqualInt(
        new BigDecimal("-12345678901234567890.123"), new BigInteger("-12345678901234567891"));
  }
}
