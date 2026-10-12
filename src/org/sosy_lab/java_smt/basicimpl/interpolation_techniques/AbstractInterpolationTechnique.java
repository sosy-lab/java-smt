/*
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.interpolation_techniques;

import com.google.common.collect.ImmutableList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractInterpolationTechnique {

  protected final FormulaManager mgr;
  protected final BooleanFormulaManager bmgr;

  protected AbstractInterpolationTechnique(FormulaManager pMgr) {
    mgr = pMgr;
    bmgr = mgr.getBooleanFormulaManager();
  }

  public abstract BooleanFormula getInterpolant(
      BooleanFormula formulasOfA, BooleanFormula formulasOfB)
      throws SolverException, InterruptedException;

  /** Extracts all variables (not UFs) from the given formula. */
  protected List<? extends Formula> getAllVariables(BooleanFormula formula) {
    return mgr.extractVariables(formula).values().asList();
  }

  /** Returns common Formulas of the 2 given lists. */
  protected List<Formula> getCommonFormulas(
      List<? extends Formula> variables1, List<? extends Formula> variables2) {
    Set<Formula> set = new LinkedHashSet<>(variables1);
    set.retainAll(variables2);
    return ImmutableList.copyOf(set);
  }

  /** Removes variablesToRemove from variablesToRemoveFrom. */
  protected List<Formula> removeVariablesFrom(
      List<? extends Formula> variablesToRemoveFrom, List<? extends Formula> variablesToRemove) {
    ImmutableList.Builder<Formula> builder = ImmutableList.builder();
    for (Formula var : variablesToRemoveFrom) {
      if (!variablesToRemove.contains(var)) {
        builder.add(var);
      }
    }
    return builder.build();
  }
}
