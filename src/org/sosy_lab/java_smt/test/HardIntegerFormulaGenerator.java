/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package org.sosy_lab.java_smt.test;

import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;

/** Generator of hard formulas using the theory of integers. */
class HardIntegerFormulaGenerator {
  private final IntegerFormulaManager ifmgr;
  private final BooleanFormulaManager bfmgr;

  private static final String CHOICE_PREFIX = "b@";
  private static final String COUNTER_PREFIX = "i@";

  HardIntegerFormulaGenerator(IntegerFormulaManager pIfmgr, BooleanFormulaManager pBfmgr) {
    ifmgr = pIfmgr;
    bfmgr = pBfmgr;
  }

  BooleanFormula generate(int n) {
    Preconditions.checkArgument(n >= 2);
    List<BooleanFormula> clauses = new ArrayList<>();
    clauses.add(ifmgr.equal(ifmgr.makeVariable(COUNTER_PREFIX + 0), ifmgr.makeNumber(0)));
    int lastIdx = 0;
    int expected = 0;
    for (int i = 1; i < 2 * n; i += 2) {
      BooleanFormula selector = bfmgr.makeVariable(CHOICE_PREFIX + i);
      clauses.add(bfmgr.or(mkConstraint(i, 3, selector), mkConstraint(i, 2, bfmgr.not(selector))));
      clauses.add(
          bfmgr.or(mkConstraint(i + 1, 3, bfmgr.not(selector)), mkConstraint(i + 1, 2, selector)));
      lastIdx = i + 1;
      expected += 5;
    }
    clauses.add(
        ifmgr.greaterThan(
            ifmgr.makeVariable(COUNTER_PREFIX + lastIdx), ifmgr.makeNumber(expected)));
    return bfmgr.and(clauses);
  }

  private BooleanFormula mkConstraint(int newIdx, int increment, BooleanFormula selector) {
    return bfmgr.and(
        selector,
        ifmgr.equal(
            ifmgr.makeVariable(COUNTER_PREFIX + newIdx),
            ifmgr.add(
                ifmgr.makeVariable(COUNTER_PREFIX + (newIdx - 1)), ifmgr.makeNumber(increment))));
  }
}
