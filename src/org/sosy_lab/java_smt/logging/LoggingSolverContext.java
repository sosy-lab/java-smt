/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.logging;

import static com.google.common.base.Preconditions.checkNotNull;

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

  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... pOptions) {
    return new LoggingProverEnvironment(logger, delegate.newProverEnvironment(pOptions));
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    return new LoggingInterpolatingProverEnvironment<>(
        logger, delegate.newProverEnvironmentWithInterpolation(options));
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    return new LoggingOptimizationProverEnvironment(
        logger, delegate.newOptimizationProverEnvironment(options));
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
}
