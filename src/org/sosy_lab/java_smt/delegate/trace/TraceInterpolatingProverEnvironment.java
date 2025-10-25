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

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class TraceInterpolatingProverEnvironment<T> extends TraceBasicProverEnvironment<T>
    implements InterpolatingProverEnvironment<T> {
  private final InterpolatingProverEnvironment<T> delegate;
  private final TraceFormulaManager mgr;
  private final TraceLogger logger;

  TraceInterpolatingProverEnvironment(
      InterpolatingProverEnvironment<T> pDelegate,
      TraceFormulaManager pFormulaManager,
      TraceLogger pLogger) {
    super(pDelegate, pFormulaManager, pLogger);
    delegate = pDelegate;
    mgr = pFormulaManager;
    logger = pLogger;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    logger.appendStmt(
        String.format(
            "%s.getInterpolant(ImmutableList.of(%s))",
            logger.toVariable(this), logger.toVariables(formulasOfA)));
    BooleanFormula itp = delegate.getInterpolant(formulasOfA);
    logger.undoLast();
    return mgr.rebuild(itp);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }
}
