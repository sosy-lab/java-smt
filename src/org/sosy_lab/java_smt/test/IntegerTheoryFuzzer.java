// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import java.util.Random;
import java.util.stream.IntStream;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/** Fuzzer over the theory of integers. */
class IntegerTheoryFuzzer {

  private final IntegerFormulaManager ifmgr;
  private IntegerFormula[] vars = new IntegerFormula[0];
  private final Random r;
  private static final String varNameTemplate = "VAR_";
  private int maxConstant;

  IntegerTheoryFuzzer(FormulaManager fmgr, Random pR) {
    ifmgr = fmgr.getIntegerFormulaManager();
    r = pR;
  }

  public IntegerFormula fuzz(int formulaSize, int pMaxConstant) {
    IntegerFormula[] args =
        IntStream.range(0, formulaSize)
            .mapToObj(i -> ifmgr.makeVariable(varNameTemplate + i))
            .toArray(IntegerFormula[]::new);
    return fuzz(formulaSize, pMaxConstant, args);
  }

  public IntegerFormula fuzz(int formulaSize, int pMaxConstant, IntegerFormula... pVars) {
    vars = pVars;
    maxConstant = pMaxConstant;
    return recFuzz(formulaSize);
  }

  private IntegerFormula recFuzz(int pFormulaSize) {
    if (pFormulaSize == 1) {

      if (r.nextBoolean()) {
        return getConstant();

      } else {
        return getVar();
      }

    } else if (pFormulaSize == 2) {
      return ifmgr.negate(getVar());
    } else {

      // One token taken by the operator.
      pFormulaSize -= 1;

      // Pivot \in [1, formulaSize - 1]
      int pivot = 1 + r.nextInt(pFormulaSize - 1);
      switch (r.nextInt(3)) {
        case 0:
          return ifmgr.add(recFuzz(pivot), recFuzz(pFormulaSize - pivot));
        case 1:
          return ifmgr.subtract(recFuzz(pivot), recFuzz(pFormulaSize - pivot));
        case 2:

          // Multiplication by a constant.
          return ifmgr.multiply(getConstant(), recFuzz(pFormulaSize - 1));
        default:
          throw new UnsupportedOperationException("Unexpected state");
      }
    }
  }

  private IntegerFormula getConstant() {
    return ifmgr.makeNumber((long) r.nextInt(2 * maxConstant) - maxConstant);
  }

  private IntegerFormula getVar() {
    return vars[r.nextInt(vars.length)];
  }
}
