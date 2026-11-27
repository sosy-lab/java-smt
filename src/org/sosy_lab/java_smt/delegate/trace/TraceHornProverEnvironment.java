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

import org.sosy_lab.java_smt.api.HornProverEnvironment;

class TraceHornProverEnvironment extends TraceBasicProverEnvironment<Void>
    implements HornProverEnvironment {

  TraceHornProverEnvironment(
      HornProverEnvironment pDelegate,
      TraceFormulaManager pFormulaManager,
      TraceLogger pLogger) {
    super(pDelegate, pFormulaManager, pLogger);
  }
}
