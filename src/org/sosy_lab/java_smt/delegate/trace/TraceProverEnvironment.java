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

import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;

public class TraceProverEnvironment extends TraceBasicProverEnvironment<Void>
    implements ProverEnvironment {
  TraceProverEnvironment(
      BasicProverEnvironment<Void> pDelegate,
      TraceFormulaManager pFormulaManager,
      TraceLogger pLogger) {
    super(pDelegate, pFormulaManager, pLogger);
  }
}
