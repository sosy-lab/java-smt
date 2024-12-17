// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.logging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/** Wrapper for an optimizing solver. */
class LoggingOptimizationProverEnvironment extends LoggingBasicProverEnvironment<Void>
    implements OptimizationProverEnvironment {

  private final OptimizationProverEnvironment wrapped;

  LoggingOptimizationProverEnvironment(LogManager logger, OptimizationProverEnvironment oe) {
    super(oe, logger);
    this.wrapped = checkNotNull(oe);
  }

  @Override
  public int maximize(Formula objective) {
    logger.log(Level.FINE, "Maximizing:", objective);
    return wrapped.maximize(objective);
  }

  @Override
  public int minimize(Formula objective) {
    logger.log(Level.FINE, "Minimizing:", objective);
    return wrapped.minimize(objective);
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    OptStatus result = wrapped.check();
    logger.log(Level.FINE, "optimization returned", result);
    return result;
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    return wrapped.upper(handle, epsilon);
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    return wrapped.lower(handle, epsilon);
  }
}
