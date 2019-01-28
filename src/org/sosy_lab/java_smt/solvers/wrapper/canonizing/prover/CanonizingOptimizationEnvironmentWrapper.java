/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.canonizing.prover;

import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingOptimizationEnvironmentWrapper extends AbstractCanonizingEnvironment<Void>
    implements OptimizationProverEnvironment {

  private OptimizationProverEnvironment delegate;

  public CanonizingOptimizationEnvironmentWrapper(
      OptimizationProverEnvironment pEnv,
      FormulaManager pFormulaManager,
      List<CanonizingStrategy> pStrategies) {
    super(pFormulaManager, pStrategies);
    delegate = pEnv;
  }

  @Override
  protected OptimizationProverEnvironment getDelegate() {
    return delegate;
  }

  @Override
  public int maximize(Formula pObjective) {
    return delegate.maximize(pObjective);
  }

  @Override
  public int minimize(Formula pObjective) {
    return delegate.minimize(pObjective);
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    return delegate.check();
  }

  @Override
  public Optional<Rational> upper(int pHandle, Rational pEpsilon) {
    return delegate.upper(pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> lower(int pHandle, Rational pEpsilon) {
    return delegate.lower(pHandle, pEpsilon);
  }
}
