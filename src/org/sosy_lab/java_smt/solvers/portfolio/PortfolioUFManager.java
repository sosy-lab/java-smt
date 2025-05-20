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
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.List;
import java.util.Map.Entry;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;

@SuppressWarnings("unchecked")
public class PortfolioUFManager implements UFManager {

  private final PortfolioFormulaCreator creator;

  protected PortfolioUFManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, List<FormulaType<?>> args) {
    checkVariableName(name);

    ImmutableMap.Builder<Solvers, FunctionDeclaration<T>> finalFormulaBuilder =
        ImmutableMap.builder();
    for (Entry<Solvers, UFManager> solverAndManager :
        creator.getSolverSpecificUfFormulaManagers().entrySet()) {
      Solvers solver = solverAndManager.getKey();
      UFManager mgr = creator.getSolverSpecificUfFormulaManagers().get(solver);

      finalFormulaBuilder.put(
          solver, checkNotNull(mgr).declareUF(name, returnType, ImmutableList.copyOf(args)));
    }

    return FunctionDeclarationImpl.of(
        name, FunctionDeclarationKind.UF, args, returnType, finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String name, FormulaType<T> returnType, FormulaType<?>... args) {
    return declareUF(name, returnType, ImmutableList.copyOf(args));
  }

  @Override
  public <T extends Formula> T callUF(
      FunctionDeclaration<T> funcType, List<? extends Formula> args) {
    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, UFManager> solverAndManager :
        creator.getSolverSpecificUfFormulaManagers().entrySet()) {
      Solvers solver = solverAndManager.getKey();
      UFManager mgr = creator.getSolverSpecificUfFormulaManagers().get(solver);

      ImmutableList.Builder<Formula> specificArgs = ImmutableList.builder();
      for (Formula pf : args) {
        assert pf instanceof PortfolioFormula;
        specificArgs.add(checkNotNull(((PortfolioFormula) pf).getFormulasPerSolver().get(solver)));
      }

      finalFormulaBuilder.put(solver, checkNotNull(mgr).callUF(funcType, specificArgs.build()));
    }

    return creator.encapsulate(funcType.getType(), finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    return callUF(funcType, ImmutableList.copyOf(args));
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    checkVariableName(name);

    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, UFManager> solverAndManager :
        creator.getSolverSpecificUfFormulaManagers().entrySet()) {
      Solvers solver = solverAndManager.getKey();
      UFManager mgr = creator.getSolverSpecificUfFormulaManagers().get(solver);

      ImmutableList.Builder<Formula> specificArgs = ImmutableList.builder();
      for (Formula pf : pArgs) {
        assert pf instanceof PortfolioFormula;
        specificArgs.add(checkNotNull(((PortfolioFormula) pf).getFormulasPerSolver().get(solver)));
      }

      finalFormulaBuilder.put(
          solver, checkNotNull(mgr).declareAndCallUF(name, pReturnType, specificArgs.build()));
    }

    return creator.encapsulate(pReturnType, finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    return declareAndCallUF(name, pReturnType, ImmutableList.copyOf(pArgs));
  }
}
