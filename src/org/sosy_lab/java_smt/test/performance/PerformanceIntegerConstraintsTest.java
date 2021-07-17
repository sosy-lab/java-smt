// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test.performance;

import org.junit.Before;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class PerformanceIntegerConstraintsTest extends AbstractPerformanceTest0 {

  @Before
  public final void checkRequirements() {
    requireIntegers();
  }

  @Override
  protected BooleanFormula createConstraint(int i) {
    return imgr.equal(imgr.makeVariable("i" + i), imgr.makeNumber(i));
  }
}
