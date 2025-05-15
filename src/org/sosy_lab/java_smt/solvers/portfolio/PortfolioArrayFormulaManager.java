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
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.collect.ImmutableMap;
import java.util.Map;
import java.util.Map.Entry;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioArrayFormula;

public class PortfolioArrayFormulaManager implements ArrayFormulaManager {

  private final Map<Solvers, ArrayFormulaManager> managers;
  private final PortfolioFormulaCreator creator;

  PortfolioArrayFormulaManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
    managers = pCreator.getSpecializedManager(FormulaManager::getArrayFormulaManager);
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {

    ImmutableMap.Builder<Solvers, Formula> finalTermBuilder = ImmutableMap.builder();
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    assert pArray instanceof PortfolioArrayFormula;
    assert pIndex instanceof PortfolioFormula;
    FormulaType<TE> elementType = null;
    for (Entry<Solvers, ArrayFormula<TI, TE>> entry1 :
        ((PortfolioArrayFormula<TI, TE>) pArray).getFormulasPerSolver().entrySet()) {
      ArrayFormula<TI, TE> arrayFormula1 = entry1.getValue();
      FormulaType<TE> elementTypeFormula = getElementType(arrayFormula1);
      if (elementType == null) {
        elementType = elementTypeFormula;
      } else {
        checkState(elementType == elementTypeFormula);
      }
      Solvers solver = entry1.getKey();
      TI indexFormula = (TI) ((PortfolioFormula) pIndex).getFormulasPerSolver().get(solver);
      if (indexFormula != null) {
        ArrayFormulaManager mgr = managers.get(solver);
        // mgr == null: ignore, theory is not supported.
        if (mgr != null) {
          // Delegate to specific solver
          finalTermBuilder.put(solver, mgr.select(arrayFormula1, indexFormula));
        }
      }
    }

    Map<Solvers, Formula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    return creator.encapsulate(elementType, finalTerm);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {

    ImmutableMap.Builder<Solvers, Formula> finalTermBuilder = ImmutableMap.builder();
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    assert pArray instanceof PortfolioArrayFormula;
    assert pIndex instanceof PortfolioFormula;
    assert pValue instanceof PortfolioFormula;
    for (Entry<Solvers, ArrayFormula<TI, TE>> arrayEntry :
        ((PortfolioArrayFormula<TI, TE>) pArray).getFormulasPerSolver().entrySet()) {
      ArrayFormula<TI, TE> arrayFormula = arrayEntry.getValue();
      Solvers solver = arrayEntry.getKey();
      TI indexFormula = (TI) ((PortfolioFormula) pIndex).getFormulasPerSolver().get(solver);
      TE valueFormula = (TE) ((PortfolioFormula) pValue).getFormulasPerSolver().get(solver);
      if (indexFormula != null && valueFormula != null) {
        ArrayFormulaManager mgr = managers.get(solver);
        // mgr == null: ignore, theory is not supported.
        if (mgr != null) {
          // Delegate to specific solver
          finalTermBuilder.put(solver, mgr.store(arrayFormula, indexFormula, valueFormula));
        }
      }
    }

    Map<Solvers, Formula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    final FormulaType<TI> indexType = creator.getArrayFormulaIndexType(pArray);
    final FormulaType<TE> elementType = creator.getArrayFormulaElementType(pArray);

    return creator.encapsulateArray(finalTerm, indexType, elementType);
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {

    checkVariableName(pName);
    ImmutableMap.Builder<Solvers, Formula> finalTermBuilder = ImmutableMap.builder();
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    for (Entry<Solvers, ArrayFormulaManager> solverAndManager : managers.entrySet()) {
      Solvers solver = solverAndManager.getKey();
      ArrayFormulaManager mgr = solverAndManager.getValue();
      // Delegate to specific solver
      finalTermBuilder.put(solver, mgr.makeArray(pName, pIndexType, pElementType));
    }

    Map<Solvers, Formula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    return creator.encapsulateArray(finalTermBuilder.buildOrThrow(), pIndexType, pElementType);
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType, TE defaultElement) {

    ImmutableMap.Builder<Solvers, Formula> finalTermBuilder = ImmutableMap.builder();
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    assert defaultElement instanceof PortfolioFormula;
    for (Entry<Solvers, ? extends Formula> entry1 :
        ((PortfolioFormula) defaultElement).getFormulasPerSolver().entrySet()) {
      TE solverSpecificDefaultElement = (TE) entry1.getValue();
      Solvers solver = entry1.getKey();
      ArrayFormulaManager mgr = managers.get(solver);
      // mgr == null: ignore, theory is not supported.
      if (mgr != null) {
        // Delegate to specific solver
        finalTermBuilder.put(
            solver, mgr.makeArray(pIndexType, pElementType, solverSpecificDefaultElement));
      }
    }

    Map<Solvers, Formula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    return creator.encapsulateArray(finalTermBuilder.buildOrThrow(), pIndexType, pElementType);
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {

    ImmutableMap.Builder<Solvers, Formula> finalTermBuilder = ImmutableMap.builder();
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    assert pArray1 instanceof PortfolioArrayFormula;
    assert pArray2 instanceof PortfolioArrayFormula;
    for (Entry<Solvers, ArrayFormula<TI, TE>> entry1 :
        ((PortfolioArrayFormula<TI, TE>) pArray1).getFormulasPerSolver().entrySet()) {
      ArrayFormula<TI, TE> arrayFormula1 = entry1.getValue();
      Solvers solver = entry1.getKey();
      ArrayFormula<TI, TE> arrayFormula2 =
          ((PortfolioArrayFormula<TI, TE>) pArray2).getFormulasPerSolver().get(solver);
      if (arrayFormula2 != null) {
        ArrayFormulaManager mgr = managers.get(solver);
        // mgr == null: ignore, theory is not supported.
        if (mgr != null) {
          // Delegate to specific solver
          finalTermBuilder.put(solver, mgr.equivalence(arrayFormula1, arrayFormula2));
        }
      }
    }

    Map<Solvers, Formula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    return creator.encapsulateBoolean(finalTerm);
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    assert pArray instanceof PortfolioArrayFormula;
    return creator.getArrayFormulaIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    assert pArray instanceof PortfolioArrayFormula;
    return creator.getArrayFormulaElementType(pArray);
  }
}
