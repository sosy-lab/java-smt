/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.basicimpl.tactics;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaManager;

public enum Tactic {
  NNF(
      "nnf",
      "Convert the formula to NNF. Equivalence, ITE and implications are resolved"
          + " by replacing them with appropriate formulas consisting of and/or/not") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      return new NNFVisitor(pFmgr).visit(pF);
    }
  },
  CNF("cnf", "Convert the formula to CNF. This tactic creates a formula which is"
      + " in some cases exponentially bigger. E.g. (x ^ y) v (z ^ w) will have"
      + " 2^n clauses in CNF afterwards.") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      BooleanFormula nnf = new NNFVisitor(pFmgr).visit(pF);
      return new CNFVisitor(pFmgr).visit(nnf);
    }
  },
  TSEITIN_CNF("tseitin-cnf", "Convert the formula to CNF using Tseitin encoding") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      throw new UnsupportedOperationException("This tactic has no default implementation.");
    }
  },
  QE_LIGHT("qe-light", "Perform light quantifier elimination") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      throw new UnsupportedOperationException("This tactic has no default implementation.");
    }
  },
  QE("qe", "Perform quantifier elimination") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      throw new UnsupportedOperationException("This tactic has no default implementation.");
    }
  };

  private final String name;
  private final String description;

  Tactic(String pName, String pDescription) {
    name = pName;
    description = pDescription;
  }

  public String getTacticName() {
    return name;
  }

  public String getDescription() {
    return description;
  }

  /**
   * Applys the default implementation for the tactic on the given Formula
   * and returns the result. Note that this may lead to different results and
   * may be not as efficient as using solver-specific tactic implementations by
   * calling {@code FormulaManager#applyTactic(BooleanFormula, Tactic)}
   */
  public abstract BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF);
}
