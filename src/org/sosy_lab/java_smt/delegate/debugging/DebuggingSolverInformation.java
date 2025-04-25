// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;

@Options(prefix = "solver.debugMode")
public class DebuggingSolverInformation {

  @Option(
      secure = true,
      description =
          "Enable assertions that make sure that solver instances are only used on the "
              + "thread that created them.")
  private boolean threadLocal = false;

  @Option(
      secure = true,
      description =
          "Enable assertions that make sure that functions are only used in the context that "
              + "declared them.")
  private boolean noSharedDeclarations = false;

  @Option(
      secure = true,
      description =
          "Enable assertions that make sure formula terms are only used in the context that "
              + "created them.")
  private boolean noSharedFormulas = false;

  // TODO: Check that the feature map is correct
  private static final Map<Solvers, Set<FunctionDeclaration<?>>> globalFunctions =
      Map.of(
          Solvers.PRINCESS,
          ConcurrentHashMap.newKeySet(),
          Solvers.YICES2,
          ConcurrentHashMap.newKeySet());

  private final Set<FunctionDeclaration<?>> declaredFunctions;

  // TODO: Check that the feature map is correct
  private static final Map<Solvers, Set<Formula>> globalTerms =
      Map.of(
          Solvers.CVC4,
          ConcurrentHashMap.newKeySet(),
          Solvers.YICES2,
          ConcurrentHashMap.newKeySet());

  private Set<Formula> definedFormulas;

  private final Thread solverThread = Thread.currentThread();

  DebuggingSolverInformation(Solvers pSolver, Configuration pConfiguration)
      throws InvalidConfigurationException {
    // Read in user supplied options
    pConfiguration.inject(this);

    // Set configuration options based on the solver that is being used. Options from the
    // configuration passed on the command line will overwrite these settings. That is, if
    // threadLocal, noSharedDeclarations or noSharedFormulas is set to 'true' we will throw an
    // exception if the forbidden feature is used, even if the solver does allow it.
    if (pSolver == Solvers.CVC5) {
      threadLocal = true;
    }
    if (!globalFunctions.containsKey(pSolver)) {
      noSharedDeclarations = true;
    }
    if (!globalTerms.containsKey(pSolver)) {
      noSharedFormulas = true;
    }

    // Initialize function declaration context
    if (noSharedDeclarations) {
      declaredFunctions = ConcurrentHashMap.newKeySet();
    } else {
      declaredFunctions = globalFunctions.getOrDefault(pSolver, ConcurrentHashMap.newKeySet());
    }

    // Initialize formula context
    if (noSharedFormulas) {
      definedFormulas = ConcurrentHashMap.newKeySet();
    } else {
      definedFormulas = globalTerms.getOrDefault(pSolver, ConcurrentHashMap.newKeySet());
    }
  }

  Thread getInitialSolverContextThread() {
    return solverThread;
  }

  boolean isThreadLocal() {
    return threadLocal;
  }

  boolean isNoSharedDeclarations() {
    return noSharedDeclarations;
  }

  boolean isNoSharedFormulas() {
    return noSharedFormulas;
  }

  public static Set<Formula> getGlobalTermsForSolver(Solvers solver) {
    return globalTerms.getOrDefault(solver, ConcurrentHashMap.newKeySet());
  }

  public static boolean solverHasSharedFormulas(Solvers solver) {
    return globalTerms.containsKey(solver);
  }

  public static Set<FunctionDeclaration<?>> getGlobalFunctionsForSolver(Solvers solver) {
    return globalFunctions.getOrDefault(solver, ConcurrentHashMap.newKeySet());
  }

  public static boolean solverHasSharedFunctions(Solvers solver) {
    return globalFunctions.containsKey(solver);
  }

  /** Needs to be called after a new function is declared to associate it with this context. */
  public void addFunctionDeclaration(FunctionDeclaration<?> pFunctionDeclaration) {
    declaredFunctions.add(pFunctionDeclaration);
  }

  Set<FunctionDeclaration<?>> getDeclaredFunctions() {
    return declaredFunctions;
  }

  void addDefinedFormula(Formula f) {
    definedFormulas.add(f);
  }

  Set<Formula> getDefinedFormulas() {
    return definedFormulas;
  }
}
