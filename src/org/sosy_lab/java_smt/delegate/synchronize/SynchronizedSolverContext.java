// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

@Options(prefix = "solver.synchronized")
public class SynchronizedSolverContext implements SolverContext {

  @Option(
      secure = true,
      description =
          "Use provers from a seperate context to solve queries. "
              + "This allows more parallelity when solving larger queries.")
  private boolean useSeperateProvers = false;

  private final SolverContext delegate;
  private final SolverContext sync;
  private final Configuration config;
  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;

  public SynchronizedSolverContext(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      SolverContext pDelegate)
      throws InvalidConfigurationException {
    pConfig.inject(this, SynchronizedSolverContext.class);
    delegate = checkNotNull(pDelegate);
    sync = delegate;
    config = pConfig;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
  }

  @SuppressWarnings("resource")
  private SolverContext createOtherContext() {
    SolverContext otherContext;
    try {
      otherContext =
          SolverContextFactory.createSolverContext(
              config, logger, shutdownNotifier, delegate.getSolverName());
    } catch (InvalidConfigurationException e) {
      throw new AssertionError("should not happen, current context was already created before.");
    }
    Preconditions.checkState(
        otherContext instanceof SynchronizedSolverContext,
        "same config implies same nesting of solver contexts.");
    return ((SynchronizedSolverContext) otherContext).delegate;
  }

  @Override
  public FormulaManager getFormulaManager() {
    return new SynchronizedFormulaManager(delegate.getFormulaManager(), delegate);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... pOptions) {
    synchronized (sync) {
      if (useSeperateProvers) {
        SolverContext otherContext = createOtherContext();
        return new SynchronizedProverEnvironmentWithContext(
            otherContext.newProverEnvironment(pOptions),
            sync,
            delegate.getFormulaManager(),
            otherContext.getFormulaManager());
      } else {
        return new SynchronizedProverEnvironment(delegate.newProverEnvironment(pOptions), delegate);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... pOptions) {
    synchronized (sync) {
      if (useSeperateProvers) {
        SolverContext otherContext = createOtherContext();
        return new SynchronizedProverEnvironmentWithContext(
            otherContext.newProverEnvironment(pProverShutdownNotifier, pOptions),
            sync,
            delegate.getFormulaManager(),
            otherContext.getFormulaManager());
      } else {
        return new SynchronizedProverEnvironment(
            delegate.newProverEnvironment(pProverShutdownNotifier, pOptions), delegate);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... pOptions) {
    synchronized (sync) {
      if (useSeperateProvers) {
        SolverContext otherContext = createOtherContext();
        return new SynchronizedInterpolatingProverEnvironmentWithContext<>(
            otherContext.newProverEnvironmentWithInterpolation(pOptions),
            sync,
            delegate.getFormulaManager(),
            otherContext.getFormulaManager());
      } else {
        return new SynchronizedInterpolatingProverEnvironment<>(
            delegate.newProverEnvironmentWithInterpolation(pOptions), delegate);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... pOptions) {
    synchronized (sync) {
      if (useSeperateProvers) {
        SolverContext otherContext = createOtherContext();
        return new SynchronizedInterpolatingProverEnvironmentWithContext<>(
            otherContext.newProverEnvironmentWithInterpolation(pProverShutdownNotifier, pOptions),
            sync,
            delegate.getFormulaManager(),
            otherContext.getFormulaManager());
      } else {
        return new SynchronizedInterpolatingProverEnvironment<>(
            delegate.newProverEnvironmentWithInterpolation(pProverShutdownNotifier, pOptions),
            delegate);
      }
    }
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... pOptions) {
    synchronized (sync) {
      // seperate prover environment not available, because we can not translate arbitrary formulae.
      // if (useSeperateProvers) { }
      return new SynchronizedOptimizationProverEnvironment(
          delegate.newOptimizationProverEnvironment(pOptions), delegate);
    }
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... pOptions) {
    synchronized (sync) {
      // seperate prover environment not available, because we can not translate arbitrary formulae.
      // if (useSeperateProvers) { }
      return new SynchronizedOptimizationProverEnvironment(
          delegate.newOptimizationProverEnvironment(pProverShutdownNotifier, pOptions), delegate);
    }
  }

  @Override
  public String getVersion() {
    synchronized (sync) {
      return delegate.getVersion();
    }
  }

  @Override
  public Solvers getSolverName() {
    synchronized (sync) {
      return delegate.getSolverName();
    }
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    synchronized (sync) {
      return delegate.getStatistics();
    }
  }

  @Override
  public void close() {
    synchronized (sync) {
      delegate.close();
    }
  }
}
