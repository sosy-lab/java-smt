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
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

class TraceHornProverEnvironment extends TraceBasicProverEnvironment<Void>
    implements HornProverEnvironment {
  private final HornProverEnvironment delegate;
  private final TraceFormulaManager mgr;
  private final TraceLogger logger;

  TraceHornProverEnvironment(
      HornProverEnvironment pDelegate,
      TraceFormulaManager pFormulaManager,
      TraceLogger pLogger) {
    super(pDelegate, pFormulaManager, pLogger);
    delegate = pDelegate;
    mgr = pFormulaManager;
    logger = pLogger;
  }
}
