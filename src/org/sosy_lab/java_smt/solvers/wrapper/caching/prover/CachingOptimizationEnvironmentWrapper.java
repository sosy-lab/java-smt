/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.caching.prover;

import java.util.Optional;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache.CachingMode;

public class CachingOptimizationEnvironmentWrapper extends AbstractCachingEnvironment<Void>
    implements OptimizationProverEnvironment {

  private OptimizationProverEnvironment delegate;

  public CachingOptimizationEnvironmentWrapper(
      OptimizationProverEnvironment pEnv,
      FormulaManager pMgr,
      CachingMode pMode,
      Configuration config)
      throws InvalidConfigurationException {
    super(pMgr, pMode, config);
    delegate = pEnv;
  }

  @Override
  protected OptimizationProverEnvironment getDelegate() {
    return delegate;
  }

  @Override
  public int maximize(Formula pObjective) {
    Integer max = cache.getFormulaMaximize(formula, pObjective);
    if (max == null) {
      max = delegate.maximize(pObjective);
      cache.storeFormulaMaximize(formula, max, pObjective);
    }
    return max;
  }

  @Override
  public int minimize(Formula pObjective) {
    Integer min = cache.getFormulaMinimize(formula, pObjective);
    if (min == null) {
      min = delegate.minimize(pObjective);
      cache.storeFormulaMinimize(formula, min, pObjective);
    }
    return min;
  }

  // FIXME: how to handle this?
  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    return delegate.check();
  }

  @Override
  public Optional<Rational> upper(int pHandle, Rational pEpsilon) {
    Optional<Rational> upper = cache.getFormulaUpper(formula, pHandle, pEpsilon);
    if (upper == null) {
      upper = delegate.upper(pHandle, pEpsilon);
      cache.storeFormulaUpper(formula, upper, pHandle, pEpsilon);
    }
    return upper;
  }

  @Override
  public Optional<Rational> lower(int pHandle, Rational pEpsilon) {
    Optional<Rational> lower = cache.getFormulaLower(formula, pHandle, pEpsilon);
    if (lower == null) {
      lower = delegate.lower(pHandle, pEpsilon);
      cache.storeFormulaLower(formula, lower, pHandle, pEpsilon);
    }
    return lower;
  }
}
