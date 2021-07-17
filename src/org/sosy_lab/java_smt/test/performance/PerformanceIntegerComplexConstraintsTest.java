// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test.performance;

import java.util.ArrayList;
import java.util.List;
import org.junit.Before;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class PerformanceIntegerComplexConstraintsTest extends AbstractPerformanceTest0 {

  @Before
  public final void checkRequirements() {
    requireIntegers();
  }

  @Override
  protected List<BooleanFormula> createConstraints() {
    List<BooleanFormula> lst = new ArrayList<>(getSymbolLimit());
    for (int i = 0; i < getSymbolLimit(); i++) {
      for (int step = 0; step < 5; step++) {
        lst.add(imgr.equal(imgr.makeVariable("i" + i), imgr.makeVariable("i" + (i + step))));
      }
    }
    return lst;
  }

  @Override
  protected BooleanFormula createConstraint(int pI) {
    throw new AssertionError("unused");
  }
}
