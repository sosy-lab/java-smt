/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.ProverEnvironment;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.logging.Level;

/**
 * Wraps a prover environment with a logging object.
 */
class LoggingProverEnvironment extends LoggingBasicProverEnvironment<Void>
    implements ProverEnvironment {

  private final ProverEnvironment wrapped;

  LoggingProverEnvironment(LogManager logger, ProverEnvironment pe) {
    super(pe, logger);
    this.wrapped = checkNotNull(pe);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    boolean result = wrapped.isUnsatWithAssumptions(assumptions);
    logger.log(Level.FINE, "unsat-check returned:", result);
    return result;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    Optional<List<BooleanFormula>> result = wrapped.unsatCoreOverAssumptions(assumptions);
    logger.log(Level.FINE, "unsat-check returned:", !result.isPresent());
    return result;
  }

  @Override
  public Model getModel() throws SolverException {
    Model m = wrapped.getModel();
    logger.log(Level.FINE, "model", m);
    return m;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    List<BooleanFormula> unsatCore = wrapped.getUnsatCore();
    logger.log(Level.FINE, "unsat-core", unsatCore);
    return unsatCore;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    T result = wrapped.allSat(callback, important);
    logger.log(Level.FINE, "allsat-result:", result);
    return result;
  }
}
