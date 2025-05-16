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

import com.google.common.collect.ImmutableMap;
import java.io.IOException;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBooleanFormula;

public class PortfolioFormulaManager
    extends AbstractFormulaManager<Map<Solvers, ? extends Formula>, Void, Void, Void> {

  private final Map<Solvers, FormulaManager> solversToFormulaManagers;

  public PortfolioFormulaManager(
      Map<Solvers, FormulaManager> pSolversFormulaManagerMap,
      PortfolioFormulaCreator creator,
      PortfolioUFManager pFunctionManager,
      PortfolioBooleanFormulaManager pBooleanManager,
      PortfolioIntegerFormulaManager pIntegerManager,
      PortfolioRationalFormulaManager pRationalManager,
      PortfolioBitvectorFormulaManager pBitpreciseManager,
      PortfolioFloatingPointFormulaManager pFloatingPointManager,
      PortfolioQuantifiedFormulaManager pQuantifiedManager,
      PortfolioArrayFormulaManager pArrayManager,
      PortfolioSLFormulaManager pSlManager,
      PortfolioStringFormulaManager pStrManager,
      PortfolioEnumerationFormulaManager pEnumerationManager) {
    /*
    super(
        creator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        pQuantifiedManager,
        pArrayManager,
        pSlManager,
        pStrManager,
        pEnumerationManager);
     */
    super(
        creator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        null,
        null,
        pArrayManager,
        null,
        null,
        null);
    solversToFormulaManagers = pSolversFormulaManagerMap;
  }

  @Override
  protected Map<Solvers, ? extends Formula> parseImpl(String formulaStr)
      throws IllegalArgumentException {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, FormulaManager> solversAndManagers : solversToFormulaManagers.entrySet()) {
      Solvers solver = solversAndManagers.getKey();
      finalFormulaBuilder.put(solver, solversAndManagers.getValue().parse(formulaStr));
    }
    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected String dumpFormulaImpl(Map<Solvers, ? extends Formula> t) throws IOException {
    Solvers solver = t.keySet().iterator().next();
    if (t.containsKey(Solvers.MATHSAT5)) {
      // MathSAT5 usually has good exports.
      solver = Solvers.MATHSAT5;
    }
    return solversToFormulaManagers
        .get(solver)
        .dumpFormula(((BooleanFormula) t.get(solver)))
        .toString();
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();

    FormulaType<T> type = getFormulaType(f);
    for (Entry<Solvers, ? extends Formula> otherSolverAndFormula :
        ((PortfolioFormula) f).getFormulasPerSolver().entrySet()) {
      Solvers solver = otherSolverAndFormula.getKey();
      FormulaManager specificFormulaManager = solversToFormulaManagers.get(solver);
      if (specificFormulaManager != null) {
        Formula substitutedSpecificFormula =
            specificFormulaManager.substitute(otherSolverAndFormula.getValue(), fromToMapping);
        FormulaType<?> specificType = getFormulaType(f);
        assert specificType == type;
        finalFormulaBuilder.put(solver, (T) substitutedSpecificFormula);
      }
    }
    return getFormulaCreator().encapsulate(type, finalFormulaBuilder.buildOrThrow());
  }

  @Override
  protected Map<Solvers, ? extends Formula> simplify(Map<Solvers, ? extends Formula> f)
      throws InterruptedException {
    ImmutableMap.Builder<Solvers, Formula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends Formula> otherSolverAndFormula : f.entrySet()) {
      Solvers solver = otherSolverAndFormula.getKey();
      FormulaManager specificFormulaManager = solversToFormulaManagers.get(solver);
      if (specificFormulaManager != null) {
        Formula simplifiedSpecificFormula =
            specificFormulaManager.simplify(otherSolverAndFormula.getValue());
        finalFormulaBuilder.put(
            solver, specificFormulaManager.simplify(otherSolverAndFormula.getValue()));
      }
    }
    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (otherManager == this) {
      return formula;
    }
    // TODO: this might fail due to translating unsupported theories.
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    if (otherManager instanceof PortfolioFormulaManager) {
      PortfolioFormulaManager otherPortfolioManager = (PortfolioFormulaManager) otherManager;
      checkState(formula instanceof PortfolioFormula);
      PortfolioFormula portfolioFormula = (PortfolioFormula) formula;
      // Try is solver based, else just use any that we know works well.
      Set<Solvers> solversOfThis = solversToFormulaManagers.keySet();
      for (Entry<Solvers, ? extends Formula> otherSolverAndFormula :
          portfolioFormula.getFormulasPerSolver().entrySet()) {
        Solvers solver = otherSolverAndFormula.getKey();
        FormulaManager formulaManagerPerSolver = solversToFormulaManagers.get(solver);
        if (formulaManagerPerSolver != null) {
          BooleanFormula translatedFormula =
              formulaManagerPerSolver.translateFrom(
                  (BooleanFormula) portfolioFormula.getFormulasPerSolver().get(solver),
                  otherPortfolioManager.solversToFormulaManagers.get(solver));
          finalFormulaBuilder.put(solver, translatedFormula);
          solversOfThis.remove(solver);
        }
      }

      // TODO: add fallback for failure.
      Solvers otherSolver =
          selectExportSolver(otherPortfolioManager.solversToFormulaManagers.keySet());
      for (Solvers solverToTranslateTo : solversOfThis) {
        finalFormulaBuilder.put(
            solverToTranslateTo,
            solversToFormulaManagers
                .get(solverToTranslateTo)
                .translateFrom(
                    (BooleanFormula) portfolioFormula.getFormulasPerSolver().get(otherSolver),
                    otherPortfolioManager.solversToFormulaManagers.get(otherSolver)));
      }
      assert finalFormulaBuilder.buildOrThrow().keySet().equals(solversToFormulaManagers.keySet());

      return new PortfolioBooleanFormula(finalFormulaBuilder.buildOrThrow());
    }

    // Translate into all solvers chosen in the portfolio
    for (Entry<Solvers, FormulaManager> solversAndMgrsToTranslateTo :
        solversToFormulaManagers.entrySet()) {
      finalFormulaBuilder.put(
          solversAndMgrsToTranslateTo.getKey(),
          solversAndMgrsToTranslateTo.getValue().translateFrom(formula, otherManager));
    }
    assert finalFormulaBuilder.buildOrThrow().keySet().equals(solversToFormulaManagers.keySet());

    return new PortfolioBooleanFormula(finalFormulaBuilder.buildOrThrow());
  }

  private Solvers selectExportSolver(Set<Solvers> pSolvers) {
    // Choose one of the better exporters first
    if (pSolvers.contains(Solvers.MATHSAT5)) {
      return Solvers.MATHSAT5;
    } else {
      // Choose any other
      return pSolvers.iterator().next();
    }
  }
}
