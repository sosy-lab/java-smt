// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.logging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

/** {@link SolverContext} that wraps all prover environments in their logging versions. */
public final class LoggingSolverContext implements SolverContext {

  private final LogManager logger;
  private final SolverContext delegate;

  public LoggingSolverContext(LogManager pLogger, SolverContext pDelegate) {
    logger = checkNotNull(pLogger);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public FormulaManager getFormulaManager() {
    return delegate.getFormulaManager();
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... pOptions) {
    return new LoggingProverEnvironment(logger, delegate.newProverEnvironment(pOptions));
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... pOptions) {
    return new LoggingProverEnvironment(
        logger, delegate.newProverEnvironment(pProverShutdownNotifier, pOptions));
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    return new LoggingInterpolatingProverEnvironment<>(
        logger, delegate.newProverEnvironmentWithInterpolation(options));
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {
    return new LoggingInterpolatingProverEnvironment<>(
        logger, delegate.newProverEnvironmentWithInterpolation(pProverShutdownNotifier, options));
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    return new LoggingOptimizationProverEnvironment(
        logger, delegate.newOptimizationProverEnvironment(options));
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {
    return new LoggingOptimizationProverEnvironment(
        logger, delegate.newOptimizationProverEnvironment(pProverShutdownNotifier, options));
  }

  @Override
  public String getVersion() {
    return delegate.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return delegate.getSolverName();
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    delegate.close();
  }
}
