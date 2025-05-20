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

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.AbstractUnspecializedFormulaManager;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBooleanFormula;

@SuppressWarnings("unchecked")
public class PortfolioFormulaManager extends AbstractUnspecializedFormulaManager
    implements FormulaManager {

  private final PortfolioFormulaCreator creator;

  private final PortfolioUFManager ufManager;
  private final PortfolioBooleanFormulaManager booleanManager;
  private final PortfolioIntegerFormulaManager integerManager;
  private final PortfolioRationalFormulaManager rationalManager;
  private final PortfolioBitvectorFormulaManager bitvectorManager;
  private final PortfolioFloatingPointFormulaManager floatingPointManager;
  private final PortfolioQuantifiedFormulaManager quantifiedManager;
  private final PortfolioArrayFormulaManager arrayManager;
  private final PortfolioSLFormulaManager slManager;
  private final PortfolioStringFormulaManager strManager;
  private final PortfolioEnumerationFormulaManager enumerationManager;

  protected PortfolioFormulaManager(
      PortfolioFormulaCreator pCreator,
      PortfolioUFManager pUfManager,
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
    ufManager = pUfManager;
    booleanManager = pBooleanManager;
    integerManager = pIntegerManager;
    rationalManager = pRationalManager;
    bitvectorManager = pBitpreciseManager;
    floatingPointManager = pFloatingPointManager;
    quantifiedManager = pQuantifiedManager;
    arrayManager = pArrayManager;
    slManager = pSlManager;
    strManager = pStrManager;
    enumerationManager = pEnumerationManager;
    creator = pCreator;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    String theory = "the theory of integer numbers";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificIntegerFormulaManagers, theory);
    return integerManager;
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    String theory = "the theory of rational numbers";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificRationalFormulaManagers, theory);
    return rationalManager;
  }

  @Override
  public BooleanFormulaManager getBooleanFormulaManager() {
    checkState(
        creator.getSolverSpecificBooleanFormulaManagers().size()
            == creator.getSolverSpecificFormulaManagers().size());
    return booleanManager;
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    String theory = "the theory of arrays";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificArrayFormulaManagers, theory);
    return arrayManager;
  }

  @Override
  public BitvectorFormulaManager getBitvectorFormulaManager() {
    String theory = "the theory of bitvectors";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificBitvectorFormulaManagers, theory);
    return bitvectorManager;
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    String theory = "the theory of floating-points";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificFloatingPointFormulaManagers, theory);
    return floatingPointManager;
  }

  @Override
  public UFManager getUFManager() {
    String theory = "the theory of uninterpreted-functions";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificUfFormulaManagers, theory);
    return ufManager;
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    String theory = "the theory of separation-logic";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificSlFormulaManagers, theory);
    return slManager;
  }

  @Override
  public QuantifiedFormulaManager getQuantifiedFormulaManager() {
    String theory = "the theory of quantification";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificQuantifiedFormulaManagers, theory);
    return quantifiedManager;
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    String theory = "the theory of strings";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificStringFormulaManagers, theory);
    return strManager;
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    String theory = "the theory of enumerations";
    creator.checkGetFormulaManager(
        PortfolioFormulaCreator::getSolverSpecificEnumerationFormulaManagers, theory);
    return enumerationManager;
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, FormulaManager> solversAndManagers :
        creator.getSolverSpecificFormulaManagers().entrySet()) {
      Solvers solver = solversAndManagers.getKey();
      finalFormulaBuilder.put(
          solver, solversAndManagers.getValue().makeVariable(formulaType, name));
    }
    return creator.encapsulate(formulaType, finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();
    outer:
    for (Entry<Solvers, FormulaManager> solversAndManagers :
        creator.getSolverSpecificFormulaManagers().entrySet()) {
      Solvers solver = solversAndManagers.getKey();
      ImmutableList.Builder<T> specArgs = ImmutableList.builder();
      for (Formula arg : args) {
        Formula specArg = ((PortfolioFormula) arg).getFormulasPerSolver().get(solver);
        if (specArg == null) {
          creator.handleUnsupportedOperationWithReason(
              solver, "UFs not supported for chosen " + "logic and solver combination");
          continue outer;
        }
        specArgs.add((T) specArg);
      }
      finalFormulaBuilder.put(
          solver, solversAndManagers.getValue().makeApplication(declaration, specArgs.build()));
    }
    return creator.encapsulate(declaration.getType(), finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    assert formula instanceof PortfolioFormula;
    return creator.getFormulaType(checkNotNull(formula));
  }

  @Override
  public BooleanFormula parse(String formulaStr) throws IllegalArgumentException {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, FormulaManager> solversAndManagers :
        creator.getSolverSpecificFormulaManagers().entrySet()) {
      Solvers solver = solversAndManagers.getKey();
      finalFormulaBuilder.put(solver, solversAndManagers.getValue().parse(formulaStr));
    }
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public Appender dumpFormula(BooleanFormula pT) {
    assert pT instanceof PortfolioBooleanFormula;
    PortfolioBooleanFormula formula = (PortfolioBooleanFormula) pT;
    Map<Solvers, BooleanFormula> specificSolvers = formula.getFormulasPerSolver();
    Solvers solver = specificSolvers.keySet().iterator().next();
    if (specificSolvers.containsKey(Solvers.MATHSAT5)) {
      // MathSAT5 usually has good exports.
      solver = Solvers.MATHSAT5;
    }
    // TODO: try to dump, catch errors, use other solver
    return creator
        .getSolverSpecificFormulaManagers()
        .get(solver)
        .dumpFormula(specificSolvers.get(solver));
  }

  @Override
  public <T extends Formula> T simplify(T input) throws InterruptedException {
    assert input instanceof PortfolioFormula;
    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();
    FormulaType<T> type = getFormulaType(input);
    for (Entry<Solvers, ? extends Formula> otherSolverAndFormula :
        ((PortfolioFormula) input).getFormulasPerSolver().entrySet()) {
      Solvers solver = otherSolverAndFormula.getKey();
      FormulaManager specificFormulaManager =
          creator.getSolverSpecificFormulaManagers().get(solver);
      finalFormulaBuilder.put(
          solver, (T) specificFormulaManager.simplify(otherSolverAndFormula.getValue()));
    }
    return creator.encapsulate(type, finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor) {}

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    assert f instanceof PortfolioFormula;
    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();

    FormulaType<T> type = getFormulaType(f);
    for (Entry<Solvers, ? extends Formula> otherSolverAndFormula :
        ((PortfolioFormula) f).getFormulasPerSolver().entrySet()) {
      Solvers solver = otherSolverAndFormula.getKey();
      FormulaManager specificFormulaManager =
          creator.getSolverSpecificFormulaManagers().get(solver);
      if (specificFormulaManager != null) {
        Formula substitutedSpecificFormula =
            specificFormulaManager.substitute(otherSolverAndFormula.getValue(), fromToMapping);
        FormulaType<?> specificType = getFormulaType(f);
        assert specificType == type;
        finalFormulaBuilder.put(solver, (T) substitutedSpecificFormula);
      }
    }
    return creator.encapsulate(type, finalFormulaBuilder.buildOrThrow());
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
      Set<Solvers> solversOfThis = creator.getSolverSpecificFormulaManagers().keySet();
      for (Entry<Solvers, ? extends Formula> otherSolverAndFormula :
          portfolioFormula.getFormulasPerSolver().entrySet()) {
        Solvers solver = otherSolverAndFormula.getKey();
        FormulaManager formulaManagerPerSolver =
            creator.getSolverSpecificFormulaManagers().get(solver);
        if (formulaManagerPerSolver != null) {
          BooleanFormula translatedFormula =
              formulaManagerPerSolver.translateFrom(
                  (BooleanFormula) portfolioFormula.getFormulasPerSolver().get(solver),
                  otherPortfolioManager.creator.getSolverSpecificFormulaManagers().get(solver));
          finalFormulaBuilder.put(solver, translatedFormula);
          solversOfThis.remove(solver);
        }
      }

      // TODO: add fallback for failure.
      Solvers otherSolver =
          selectExportSolver(
              otherPortfolioManager.creator.getSolverSpecificFormulaManagers().keySet());
      for (Solvers solverToTranslateTo : solversOfThis) {
        finalFormulaBuilder.put(
            solverToTranslateTo,
            creator
                .getSolverSpecificFormulaManagers()
                .get(solverToTranslateTo)
                .translateFrom(
                    (BooleanFormula) portfolioFormula.getFormulasPerSolver().get(otherSolver),
                    otherPortfolioManager
                        .creator
                        .getSolverSpecificFormulaManagers()
                        .get(otherSolver)));
      }
      assert finalFormulaBuilder
          .buildOrThrow()
          .keySet()
          .equals(creator.getSolverSpecificFormulaManagers().keySet());

      return new PortfolioBooleanFormula(finalFormulaBuilder.buildOrThrow());
    }

    // Translate into all solvers chosen in the portfolio
    for (Entry<Solvers, FormulaManager> solversAndMgrsToTranslateTo :
        creator.getSolverSpecificFormulaManagers().entrySet()) {
      finalFormulaBuilder.put(
          solversAndMgrsToTranslateTo.getKey(),
          solversAndMgrsToTranslateTo.getValue().translateFrom(formula, otherManager));
    }
    assert finalFormulaBuilder
        .buildOrThrow()
        .keySet()
        .equals(creator.getSolverSpecificFormulaManagers().keySet());

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
