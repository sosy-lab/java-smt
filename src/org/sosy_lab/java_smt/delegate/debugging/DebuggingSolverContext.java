// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

// TODO: Figure out what to do about boolector (does not support visitors..)
// TODO: Add an option that checks if sorts were created on the context

@Options(prefix = "solver.debugMode")
public class DebuggingSolverContext extends DefaultFormulaVisitor<TraversalProcess>
    implements SolverContext {
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

  private final Thread solverThread = Thread.currentThread();

  // TODO: Check that the feature map is correct
  private static final Map<Solvers, Set<FunctionDeclaration<?>>> globalFunctions =
      Map.of(
          Solvers.PRINCESS,
          ConcurrentHashMap.newKeySet(),
          Solvers.CVC5,
          ConcurrentHashMap.newKeySet(),
          Solvers.YICES2,
          ConcurrentHashMap.newKeySet());

  private final Set<FunctionDeclaration<?>> declaredFunctions;

  // TODO: Check that the feature map is correct
  private static final Map<Solvers, Set<Formula>> globalTerms =
      Map.of(
          Solvers.CVC4,
          ConcurrentHashMap.newKeySet(),
          Solvers.CVC5,
          ConcurrentHashMap.newKeySet(),
          Solvers.YICES2,
          ConcurrentHashMap.newKeySet());

  private final Set<Formula> definedFormulas;

  private final SolverContext delegate;

  /** Assert that this object is only used by the thread that created it. */
  public void assertThreadLocal() {
    if (threadLocal) {
      Thread currentThread = Thread.currentThread();
      Preconditions.checkState(
          currentThread.equals(solverThread),
          "Solver instance was not created on this thread. This is thread %s, but the solver "
              + "instance belongs to thread %s.",
          currentThread.getName(),
          solverThread.getName());
    }
  }

  /** Needs to be called after a new function is declared to associate it with this context. */
  public void addFunctionDeclaration(FunctionDeclaration<?> pFunctionDeclaration) {
    declaredFunctions.add(pFunctionDeclaration);
  }

  /** Assert that the function declaration belongs to this context. */
  public void assertDeclarationInContext(FunctionDeclaration<?> pFunctionDeclaration) {
    if (List.of(FunctionDeclarationKind.VAR, FunctionDeclarationKind.UF)
        .contains(pFunctionDeclaration.getKind())) {
      Preconditions.checkArgument(
          declaredFunctions.contains(pFunctionDeclaration),
          "Function was not declared "
              + (noSharedDeclarations ? "in this context." : "on this solver.")
              + "\n%s"
              + "\nnot in"
              + "\n%s",
          pFunctionDeclaration,
          declaredFunctions);
    }
  }

  @Override
  protected TraversalProcess visitDefault(Formula f) {
    // Used in addFormulaTerm where we recursively add all sub terms of a formula to the context
    definedFormulas.add(f);
    return TraversalProcess.CONTINUE;
  }

  /** Needs to be called after a new Formula is created to associate it with this context. */
  public void addFormulaTerm(Formula pFormula) {
    delegate.getFormulaManager().visitRecursively(pFormula, this);
  }

  /** Assert that the formula belongs to this context. */
  public void assertFormulaInContext(Formula pFormula) {
    Preconditions.checkArgument(
        definedFormulas.contains(pFormula),
        "Function was not declared "
            + (noSharedDeclarations ? "in this context." : "on this solver.")
            + "\n%s"
            + "\nnot in"
            + "\n%s",
        pFormula,
        definedFormulas);
  }

  public DebuggingSolverContext(
      Solvers pSolver, Configuration pConfiguration, SolverContext pDelegate)
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

    delegate = checkNotNull(pDelegate);
  }

  @Override
  public FormulaManager getFormulaManager() {
    assertThreadLocal();
    return new DebuggingFormulaManager(delegate.getFormulaManager(), this);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    assertThreadLocal();
    return new DebuggingProverEnvironment(delegate.newProverEnvironment(options), this);
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    assertThreadLocal();
    return new DebuggingInterpolatingProverEnvironment<>(
        delegate.newProverEnvironmentWithInterpolation(options), this);
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    assertThreadLocal();
    return new DebuggingOptimizationProverEnvironment(
        delegate.newOptimizationProverEnvironment(options), this);
  }

  @Override
  public String getVersion() {
    assertThreadLocal();
    return delegate.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    assertThreadLocal();
    return delegate.getSolverName();
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    assertThreadLocal();
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    assertThreadLocal();
    delegate.close();
  }
}
