// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import java.util.Map;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

public class StatisticsSolverContext implements SolverContext {

  private final SolverContext delegate;
  private final SolverStatistics stats = new SolverStatistics();

  public StatisticsSolverContext(SolverContext pDelegate) {
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public FormulaManager getFormulaManager() {
    return new StatisticsFormulaManager(delegate.getFormulaManager(), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... pOptions) {
    return new StatisticsProverEnvironment(delegate.newProverEnvironment(pOptions), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... pOptions) {
    return new StatisticsProverEnvironment(
        delegate.newProverEnvironment(pProverShutdownNotifier, pOptions), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... pOptions) {
    return new StatisticsInterpolatingProverEnvironment<>(
        delegate.newProverEnvironmentWithInterpolation(pOptions), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {
    return new StatisticsInterpolatingProverEnvironment<>(
        delegate.newProverEnvironmentWithInterpolation(pProverShutdownNotifier, options), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... pOptions) {
    return new StatisticsOptimizationProverEnvironment(
        delegate.newOptimizationProverEnvironment(pOptions), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {
    return new StatisticsOptimizationProverEnvironment(
        delegate.newOptimizationProverEnvironment(pProverShutdownNotifier, options), stats);
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
    ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
    builder.putAll(delegate.getStatistics());
    for (Map.Entry<String, Object> entry : getSolverStatistics().asMap().entrySet()) {
      builder.put(entry.getKey(), entry.getValue().toString());
    }
    return builder.buildOrThrow();
  }

  @Override
  public void close() {
    delegate.close();
  }

  /** export statistics about the solver interaction. */
  public SolverStatistics getSolverStatistics() {
    return stats;
  }
}
