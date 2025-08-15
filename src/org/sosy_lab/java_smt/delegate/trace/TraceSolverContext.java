/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

public class TraceSolverContext implements SolverContext {
  private final SolverContext delegate;
  private final TraceLogger logger;

  public TraceSolverContext(SolverContext pDelegate) {
    delegate = pDelegate;
    // FIXME Move the files to the output folder?
    logger =
        new TraceLogger(
            "trace" + Integer.toUnsignedString(System.identityHashCode(this)) + ".java");
  }

  @Override
  public FormulaManager getFormulaManager() {
    return new TraceFormulaManager(delegate.getFormulaManager(), logger);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    return logger.logDef(
        "context",
        String.format(
            "newProverEnvironment(%s)",
            Joiner.on(", ").join(FluentIterable.from(options).transform(Enum::toString))),
        () -> new TraceProverEnvironment(delegate.newProverEnvironment(options), logger));
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    throw new UnsupportedOperationException();
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    throw new UnsupportedOperationException();
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
    logger.logStmt("context", "close()", delegate::close);
  }
}
