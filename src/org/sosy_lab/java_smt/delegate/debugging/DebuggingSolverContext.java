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
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

// TODO: Figure out what to do about boolector (does not support visitors..)
// TODO: Add an option that checks if sorts were created on the context

public class DebuggingSolverContext implements SolverContext {
  private final SolverContext delegate;
  private final DebuggingContext debugging;

  public DebuggingSolverContext(
      Solvers pSolver, Configuration pConfiguration, SolverContext pDelegate)
      throws InvalidConfigurationException {
    delegate = checkNotNull(pDelegate);
    debugging = new DebuggingContext(pSolver, pConfiguration, pDelegate.getFormulaManager());
  }

  @Override
  public FormulaManager getFormulaManager() {
    debugging.assertThreadLocal();
    return new DebuggingFormulaManager(delegate.getFormulaManager(), debugging);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    debugging.assertThreadLocal();
    return new DebuggingProverEnvironment(delegate.newProverEnvironment(options), debugging);
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    debugging.assertThreadLocal();
    return new DebuggingInterpolatingProverEnvironment<>(
        delegate.newProverEnvironmentWithInterpolation(options), debugging);
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    debugging.assertThreadLocal();
    return new DebuggingOptimizationProverEnvironment(
        delegate.newOptimizationProverEnvironment(options), debugging);
  }

  @Override
  public String getVersion() {
    debugging.assertThreadLocal();
    return delegate.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    debugging.assertThreadLocal();
    return delegate.getSolverName();
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    debugging.assertThreadLocal();
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    debugging.assertThreadLocal();
    delegate.close();
  }
}
