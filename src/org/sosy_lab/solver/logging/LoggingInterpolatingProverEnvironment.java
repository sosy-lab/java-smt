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
package org.sosy_lab.solver.logging;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

class LoggingInterpolatingProverEnvironment<T> extends LoggingBasicProverEnvironment<T>
    implements InterpolatingProverEnvironmentWithAssumptions<T> {

  private final InterpolatingProverEnvironmentWithAssumptions<T> wrapped;

  LoggingInterpolatingProverEnvironment(
      LogManager logger, InterpolatingProverEnvironmentWithAssumptions<T> ipe) {
    super(ipe, logger);
    this.wrapped = checkNotNull(ipe);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "assumptions:", pAssumptions);
    boolean result = wrapped.isUnsatWithAssumptions(pAssumptions);
    logger.log(Level.FINE, "unsat-check returned:", result);
    return result;
  }

  @Override
  public BooleanFormula getInterpolant(List<T> formulasOfA)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "formulasOfA:", formulasOfA);
    BooleanFormula bf = wrapped.getInterpolant(formulasOfA);
    logger.log(Level.FINE, "interpolant:", bf);
    return bf;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "formulasOfA:", partitionedFormulas);
    List<BooleanFormula> bf = wrapped.getSeqInterpolants(partitionedFormulas);
    logger.log(Level.FINE, "interpolants:", bf);
    return bf;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "formulasOfA:", partitionedFormulas);
    logger.log(Level.FINE, "startOfSubTree:", startOfSubTree);
    List<BooleanFormula> bf = wrapped.getTreeInterpolants(partitionedFormulas, startOfSubTree);
    logger.log(Level.FINE, "interpolants:", bf);
    return bf;
  }
}
