// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;

/** Generator of hard formulas using the theory of bitvectors. */
class HardBitvectorFormulaGenerator {
  private final BitvectorFormulaManager bvmgr;
  private final BooleanFormulaManager bfmgr;

  private static final String CHOICE_PREFIX = "bool@";
  private static final String COUNTER_PREFIX = "bv@";
  // Set width accordingly
  private static final int BITVECTOR_WIDTH = 32;

  HardBitvectorFormulaGenerator(BitvectorFormulaManager pBvmgr, BooleanFormulaManager pBfmgr) {
    bvmgr = pBvmgr;
    bfmgr = pBfmgr;
  }

  BooleanFormula generate(int n) {
    Preconditions.checkArgument(n >= 2);
    List<BooleanFormula> clauses = new ArrayList<>();
    clauses.add(
        bvmgr.equal(
            bvmgr.makeVariable(BITVECTOR_WIDTH, COUNTER_PREFIX + 0),
            bvmgr.makeBitvector(BITVECTOR_WIDTH, 0)));
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
        bvmgr.greaterThan(
            bvmgr.makeVariable(BITVECTOR_WIDTH, COUNTER_PREFIX + lastIdx),
            bvmgr.makeBitvector(BITVECTOR_WIDTH, expected),
            false));
    return bfmgr.and(clauses);
  }

  private BooleanFormula mkConstraint(int newIdx, int increment, BooleanFormula selector) {
    return bfmgr.and(
        selector,
        bvmgr.equal(
            bvmgr.makeVariable(BITVECTOR_WIDTH, COUNTER_PREFIX + newIdx),
            bvmgr.add(
                bvmgr.makeVariable(BITVECTOR_WIDTH, COUNTER_PREFIX + (newIdx - 1)),
                bvmgr.makeBitvector(BITVECTOR_WIDTH, increment))));
  }
}
