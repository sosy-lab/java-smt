// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import com.google.common.base.Preconditions;
import java.util.List;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

class DebuggingContext {
  // The associated formula manager. Needed in addFormulaTerm to recursively iterate over all
  // sub formulas.
  private final FormulaManager formulaManager;

  private final DebuggingSolverInformation debugInfo;

  DebuggingContext(Solvers pSolver, Configuration pConfiguration, FormulaManager pFormulaManager)
      throws InvalidConfigurationException {
    debugInfo = new DebuggingSolverInformation(pSolver, pConfiguration);
    formulaManager = pFormulaManager;
  }

  /** Assert that this object is only used by the thread that created it. */
  public void assertThreadLocal() {
    if (debugInfo.isThreadLocal()) {
      Thread currentThread = Thread.currentThread();
      Thread initialThread = debugInfo.getInitialSolverContextThread();
      Preconditions.checkState(
          currentThread.equals(initialThread),
          "Solver instance was not created on this thread. This is thread %s, but the solver "
              + "instance belongs to thread %s.",
          currentThread.getName(),
          initialThread.getName());
    }
  }

  /** Needs to be called after a new function is declared to associate it with this context. */
  public void addFunctionDeclaration(FunctionDeclaration<?> pFunctionDeclaration) {
    debugInfo.getDeclaredFunctions().add(pFunctionDeclaration);
  }

  /** Assert that the function declaration belongs to this context. */
  public void assertDeclarationInContext(FunctionDeclaration<?> pFunctionDeclaration) {
    if (List.of(FunctionDeclarationKind.VAR, FunctionDeclarationKind.UF)
        .contains(pFunctionDeclaration.getKind())) {
      Preconditions.checkArgument(
          debugInfo.getDeclaredFunctions().contains(pFunctionDeclaration),
          "Function was not declared "
              + (debugInfo.isNoSharedDeclarations() ? "in this context." : "on this solver.")
              + "\n%s"
              + "\nnot in"
              + "\n%s",
          pFunctionDeclaration,
          debugInfo.getDeclaredFunctions());
    }
  }

  /** Needs to be called after a new Formula is created to associate it with this context. */
  public void addFormulaTerm(Formula pFormula) {
    formulaManager.visitRecursively(
        pFormula,
        new DefaultFormulaVisitor<>() {
          @Override
          protected TraversalProcess visitDefault(Formula f) {
            // Recursively add all sub terms of a formula to the context
            debugInfo.getDefinedFormulas().add(f);
            return TraversalProcess.CONTINUE;
          }
        });
  }

  /** Assert that the formula belongs to this context. */
  public void assertFormulaInContext(Formula pFormula) {
    Preconditions.checkArgument(
        debugInfo.getDefinedFormulas().contains(pFormula),
        "Function was not declared "
            + (debugInfo.isNoSharedFormulas() ? "in this context." : "on this solver.")
            + "\n%s"
            + "\nnot in"
            + "\n%s",
        pFormula,
        debugInfo.getDefinedFormulas());
  }
}
