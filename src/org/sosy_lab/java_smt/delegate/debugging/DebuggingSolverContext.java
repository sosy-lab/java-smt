// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

// TODO: Add configuration options to enable/disable some of the checks
public class DebuggingSolverContext extends ThreadChecks implements SolverContext {
  private final NodeManager nodeManager = new NodeManager();
  private final SolverContext delegate;

  public final class NodeManager extends DefaultFormulaVisitor<TraversalProcess> {
    private final Set<FunctionDeclaration<?>> declaredFunctions = ConcurrentHashMap.newKeySet();
    private final Set<Formula> formulaTerms = ConcurrentHashMap.newKeySet();

    public void addFunctionDeclaration(FunctionDeclaration<?> pFunctionDeclaration) {
      declaredFunctions.add(pFunctionDeclaration);
    }

    public boolean isInFunctionDeclarations(FunctionDeclaration<?> pFunctionDeclaration) {
      return declaredFunctions.contains(pFunctionDeclaration);
    }

    public Iterable<FunctionDeclaration<?>> listFunctionDeclarations() {
      return declaredFunctions;
    }

    @Override
    protected TraversalProcess visitDefault(Formula f) {
      formulaTerms.add(f);
      return TraversalProcess.CONTINUE;
    }

    public void addFormulaTerm(Formula pFormula) {
      // We're adding the formula recursively, along with all of its sub terms
      delegate.getFormulaManager().visitRecursively(pFormula, this);
    }

    public boolean isInFormulaTerms(Formula pFormula) {
      return formulaTerms.contains(pFormula);
    }

    public Iterable<Formula> listFormulaTerms() {
      return formulaTerms;
    }
  }

  public DebuggingSolverContext(SolverContext pDelegate) {
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public FormulaManager getFormulaManager() {
    assertThreadLocal();
    return new DebuggingFormulaManager(delegate.getFormulaManager(), nodeManager);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    assertThreadLocal();
    return new DebuggingProverEnvironment(delegate.newProverEnvironment(options), nodeManager);
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    assertThreadLocal();
    return new DebuggingInterpolatingProverEnvironment<>(
        delegate.newProverEnvironmentWithInterpolation(options), nodeManager);
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    assertThreadLocal();
    return new DebuggingOptimizationProverEnvironment(
        delegate.newOptimizationProverEnvironment(options), nodeManager);
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
