// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.logging;

import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;

/** Wraps a prover environment with a logging object. */
class LoggingProverEnvironment extends LoggingBasicProverEnvironment<Void>
    implements ProverEnvironment {

  LoggingProverEnvironment(LogManager logger, ProverEnvironment pe) {
    super(pe, logger);
  }
}
