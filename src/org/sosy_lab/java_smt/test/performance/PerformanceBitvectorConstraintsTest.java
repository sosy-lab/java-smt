// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test.performance;

import com.google.common.base.Preconditions;
import org.junit.Before;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class PerformanceBitvectorConstraintsTest extends AbstractPerformanceTest0 {

  private static final int BITSIZE = 16;

  @Before
  public final void checkRequirements() {
    Preconditions.checkState(1L << BITSIZE > getSymbolLimit());
    requireBitvectors();
  }

  @Override
  protected BooleanFormula createConstraint(int i) {
    return bvmgr.equal(bvmgr.makeVariable(BITSIZE, "i" + i), bvmgr.makeBitvector(BITSIZE, i));
  }
}
