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
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/** Wrapper for a horn solver. */
class LoggingHornProverEnvironment extends LoggingBasicProverEnvironment<Void>
    implements HornProverEnvironment {

  private final HornProverEnvironment delegate;

  LoggingHornProverEnvironment(LogManager logger, HornProverEnvironment delegate) {
    super(delegate, logger);
    this.delegate = checkNotNull(delegate);
  }
}
