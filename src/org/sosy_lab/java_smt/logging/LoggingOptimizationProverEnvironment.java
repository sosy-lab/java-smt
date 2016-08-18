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
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

import java.util.Optional;
import java.util.logging.Level;

/**
 * Wrapper for an optimizing solver.
 */
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
