/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBooleanFormula;

@SuppressWarnings("unchecked")
public class PortfolioQuantifiedFormulaManager implements QuantifiedFormulaManager {

  private final PortfolioFormulaCreator creator;

  protected PortfolioQuantifiedFormulaManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    checkState(pBody instanceof PortfolioBooleanFormula);
    ImmutableMap.Builder<Solvers, BooleanFormula> resultFormulaBuilder = ImmutableMap.builder();
    outer:
    for (Entry<Solvers, QuantifiedFormulaManager> solverAndManager :
        creator.getSolverSpecificQuantifiedFormulaManagers().entrySet()) {
      Solvers solver = solverAndManager.getKey();
      QuantifiedFormulaManager manager = solverAndManager.getValue();
      BooleanFormula bodyForSolver =
          ((PortfolioBooleanFormula) pBody).getFormulasPerSolver().get(solver);
      ImmutableList.Builder<Formula> specificArgsBuilder = ImmutableList.builder();
      for (Formula f : pVariables) {
        assert f instanceof PortfolioFormula;
        Map<Solvers, ? extends Formula> solverSpecificFormula =
            ((PortfolioFormula) f).getFormulasPerSolver();
        if (!solverSpecificFormula.containsKey(solver)) {
          // Theory not supported, argument incomplete
          creator.handleUnsupportedOperationWithReason(
              solver, "error in argument of quantified" + " formula");
          continue outer;
        }
        specificArgsBuilder.add(solverSpecificFormula.get(solver));
      }
      List<? extends Formula> specificArgs = specificArgsBuilder.build();
      if (bodyForSolver != null) {
        resultFormulaBuilder.put(solver, manager.mkQuantifier(q, specificArgs, bodyForSolver));
      }
      // Do nothing, theory not supported
      creator.handleUnsupportedOperationWithReason(
          solver,
          "quantified formula creation not " + "supported due to problem with body formula");
    }
    return creator.encapsulateBoolean(resultFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    checkState(pF instanceof PortfolioBooleanFormula);
    ImmutableMap.Builder<Solvers, BooleanFormula> resultFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, QuantifiedFormulaManager> solverAndManager :
        creator.getSolverSpecificQuantifiedFormulaManagers().entrySet()) {
      Solvers solver = solverAndManager.getKey();
      QuantifiedFormulaManager manager = solverAndManager.getValue();
      BooleanFormula formulaForSolver =
          ((PortfolioBooleanFormula) pF).getFormulasPerSolver().get(solver);
      if (formulaForSolver != null) {
        resultFormulaBuilder.put(solver, manager.eliminateQuantifiers(formulaForSolver));
      }
      // Do nothing, theory not supported
      creator.handleUnsupportedOperationWithReason(
          solver, "quantified formula could not be " + "eliminated as ");
    }
    return creator.encapsulateBoolean(resultFormulaBuilder.buildOrThrow());
  }
}
