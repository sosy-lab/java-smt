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

import com.google.common.collect.Iterables;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FormulaManager;

import java.util.List;

/**
 * Enum that holds all the values for tactics that are either supported with a
 * default implementation in java-smt or with a solver-specific version e.g.
 * via z3.
 */
public enum Tactic {

  /**
   * Convert the formula to NNF. Equivalence, ITE and implications are resolved"
   * by replacing them with appropriate formulas consisting of and/or/not.
   *
   * <p>This tactic has a default implementation.</p>
   */
  NNF(
      "nnf",
      "Convert the formula to NNF. Equivalence, ITE and implications are resolved"
          + " by replacing them with appropriate formulas consisting of and/or/not") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      return new NNFVisitor(pFmgr).visit(pF);
    }
  },

  /**
   * Convert the formula to an approximated CNF. This tactic creates a CNF formula
   * but still may have some 'ands' which are deeper stacked in the formula and
   * thus would create too much conjuncts when creating a full CNF.
   *
   * <p>This tactic has a default implementation.</p>
   */
  CNF_LIGHT(
      "cnf",
      "Convert the formula to an approximated CNF. This tactic creates a CNF formula"
          + " but still may have some 'ands' which are deeper stacked in the formula and"
          + " thus would create too much conjuncts when creating a full CNF.") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      BooleanFormula nnf = new NNFVisitor(pFmgr).visit(pF);
      // TODO make the maximum depth configurable
      List<BooleanFormula> conjuncts = new CNFVisitor(pFmgr, 3).visit(nnf);
      if (conjuncts.size() == 1) {
        return Iterables.getOnlyElement(conjuncts);
      } else {
        return pFmgr.getBooleanFormulaManager().and(conjuncts);
      }
    }
  },

  /**
   * Convert the formula to CNF. This tactic creates a formula which is
   * in some cases exponentially bigger. E.g. (x /\ y) \/ (z /\ w) will have
   * 2^n clauses in CNF afterwards.
   *
   * <p>This tactic has a default implementation.</p>
   */
  CNF(
      "cnf",
      "Convert the formula to CNF. This tactic creates a formula which is"
          + " in some cases exponentially bigger. E.g. (x /\\ y) \\/ (z /\\ w) will have"
          + " 2^n clauses in CNF afterwards.") {
    @Override
    public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
      BooleanFormula nnf = new NNFVisitor(pFmgr).visit(pF);
      List<BooleanFormula> conjuncts = new CNFVisitor(pFmgr, -1).visit(nnf);
      if (conjuncts.size() == 1) {
        return Iterables.getOnlyElement(conjuncts);
      } else {
        return pFmgr.getBooleanFormulaManager().and(conjuncts);
      }
    }
  },

  /**
   * Convert the formula to CNF using Tseitin encoding. Note that the resulting
   * formula is not equivalent but only equisatisfiable.
   *
   * <p>This tactic has no default implementation.</p>
   */
  TSEITIN_CNF(
      "tseitin-cnf",
      "Convert the formula to CNF using Tseitin encoding. Note that the resulting"
          + " formula is not equivalent but only equisatisfiable."),

  /**
   * Perform light quantifier elimination.
   *
   * <p>This tactic has no default implementation.</p>
   */
  QE_LIGHT("qe-light", "Perform light quantifier elimination"),

  /**
   * Perform quantifier elimination.
   *
   * <p>This tactic has no default implementation.</p>
   */
  QE("qe", "Perform quantifier elimination");

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
   * Applies the default implementation for the tactic on the given Formula
   * and returns the result. Note that this may lead to different results and
   * may be not as efficient as using solver-specific tactic implementations by
   * calling {@code FormulaManager#applyTactic(BooleanFormula, Tactic)}.
   *
   * <p>Thus calling this method is discouraged.
   *
   * @param pFmgr The formula manager that created the given formula.
   * @param pF The formula to rewrite.
   */
  public BooleanFormula applyDefault(FormulaManager pFmgr, BooleanFormula pF) {
    throw new UnsupportedOperationException(
        String.format(
            "The tactic %s is not supported by the current solver has no default implementation.",
            getTacticName()));
  }
}
