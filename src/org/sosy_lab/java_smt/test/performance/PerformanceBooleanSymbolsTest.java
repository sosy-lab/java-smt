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
import org.sosy_lab.java_smt.api.BooleanFormula;

public class PerformanceBooleanSymbolsTest extends AbstractPerformanceTest0 {

  // booleans are so simple, lets produce more of them.
  private static final int MULTIPLIER = 5;

  @Override
  protected List<BooleanFormula> createConstraints() {
    List<BooleanFormula> lst = new ArrayList<>(getSymbolLimit());
    for (int i = 0; i < MULTIPLIER * getSymbolLimit(); i++) {
      lst.add(createConstraint(i));
    }
    return lst;
  }

  @Override
  protected BooleanFormula createConstraint(int i) {
    return bmgr.makeVariable("b" + i);
  }
}
