/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

class TraceOptimizationProverEnvironment extends TraceBasicProverEnvironment<Void>
    implements OptimizationProverEnvironment {

  private final OptimizationProverEnvironment delegate;
  private final TraceLogger logger;

  TraceOptimizationProverEnvironment(
      OptimizationProverEnvironment pDelegate,
      TraceFormulaManager pFormulaManager,
      TraceLogger pLogger) {
    super(pDelegate, pFormulaManager, pLogger);
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public int maximize(Formula objective) {
    return logger.logDefKeep(
        logger.toVariable(this),
        "maximize(%s)".formatted(logger.toVariable(objective)),
        () -> delegate.maximize(objective));
  }

  @Override
  public int minimize(Formula objective) {
    return logger.logDefKeep(
        logger.toVariable(this),
        "minimize(%s)".formatted(logger.toVariable(objective)),
        () -> delegate.minimize(objective));
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    return logger.logDefKeep(logger.toVariable(this), "check()", delegate::check);
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "upper(%d, Rational.of(\"%s\"))".formatted(handle, epsilon),
        () -> delegate.upper(handle, epsilon));
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "lower(%d, Rational.of(\"%s\"))".formatted(handle, epsilon),
        () -> delegate.lower(handle, epsilon));
  }
}
