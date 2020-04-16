/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

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
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... pOptions) {
    return new StatisticsInterpolatingProverEnvironment<>(
        delegate.newProverEnvironmentWithInterpolation(pOptions), stats);
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... pOptions) {
    return new StatisticsOptimizationProverEnvironment(
        delegate.newOptimizationProverEnvironment(pOptions), stats);
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
  public void close() {
    delegate.close();
  }

  /** export statistics about the solver interaction. */
  public SolverStatistics getSolverStatistics() {
    return stats;
  }
}
