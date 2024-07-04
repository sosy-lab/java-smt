// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.logging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.InterpolationPoint;
import org.sosy_lab.java_smt.api.SolverException;

class LoggingInterpolatingProverEnvironment<T>
    extends LoggingBasicProverEnvironment<InterpolationPoint<T>>
    implements InterpolatingProverEnvironment<T> {

  private final InterpolatingProverEnvironment<T> wrapped;

  LoggingInterpolatingProverEnvironment(LogManager logger, InterpolatingProverEnvironment<T> ipe) {
    super(ipe, logger);
    this.wrapped = checkNotNull(ipe);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<InterpolationPoint<T>> formulasOfA)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "formulasOfA:", formulasOfA);
    BooleanFormula bf = wrapped.getInterpolant(formulasOfA);
    logger.log(Level.FINE, "interpolant:", bf);
    return bf;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<InterpolationPoint<T>>> partitionedFormulas)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "formulasOfA:", partitionedFormulas);
    List<BooleanFormula> bf = wrapped.getSeqInterpolants(partitionedFormulas);
    logger.log(Level.FINE, "interpolants:", bf);
    return bf;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<InterpolationPoint<T>>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "formulasOfA:", partitionedFormulas);
    logger.log(Level.FINE, "startOfSubTree:", startOfSubTree);
    List<BooleanFormula> bf = wrapped.getTreeInterpolants(partitionedFormulas, startOfSubTree);
    logger.log(Level.FINE, "interpolants:", bf);
    return bf;
  }
}
