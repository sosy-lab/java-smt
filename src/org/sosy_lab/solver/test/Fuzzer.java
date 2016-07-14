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

package org.sosy_lab.solver.test;

import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;

import java.util.Random;

/**
 * Boolean fuzzer, useful for testing.
 */
class Fuzzer {
  private final BooleanFormulaManager bfmgr;

  private final UniqueIdGenerator idGenerator;
  private BooleanFormula[] vars = new BooleanFormula[0];
  private final Random r;

  private static final String varNameTemplate = "VAR_";

  Fuzzer(FormulaManager pFmgr, Random pRandom) {
    bfmgr = pFmgr.getBooleanFormulaManager();
    idGenerator = new UniqueIdGenerator();
    r = pRandom;
  }

  public BooleanFormula fuzz(int formulaSize, int maxNoVars) {
    vars = new BooleanFormula[maxNoVars];
    populateVars();
    return recFuzz(formulaSize);
  }

  public BooleanFormula fuzz(int formulaSize, BooleanFormula... pVars) {
    vars = pVars;
    return recFuzz(formulaSize);
  }

  private BooleanFormula recFuzz(int formulaSize) {
    if (formulaSize == 1) {

      // The only combination of size 1.
      return getVar();
    } else if (formulaSize == 2) {

      // The only combination of size 2.
      return bfmgr.not(getVar());
    } else {
      formulaSize -= 1;

      int pivot = formulaSize / 2;
      switch (r.nextInt(3)) {
        case 0:
          return bfmgr.or(recFuzz(pivot), recFuzz(formulaSize - pivot));
        case 1:
          return bfmgr.and(recFuzz(pivot), recFuzz(formulaSize - pivot));
        case 2:
          return bfmgr.not(recFuzz(formulaSize));
        default:
          throw new UnsupportedOperationException("Unexpected state");
      }
    }
  }

  private BooleanFormula getVar() {
    return vars[r.nextInt(vars.length)];
  }

  private void populateVars() {
    for (int i = 0; i < vars.length; i++) {
      vars[i] = getNewVar();
    }
  }

  private BooleanFormula getNewVar() {
    return bfmgr.makeVariable(varNameTemplate + idGenerator.getFreshId());
  }
}
