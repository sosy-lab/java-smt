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

package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.cache.CachingOptimizationProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.cache.OptimizationQuery;
import org.sosy_lab.java_smt.basicimpl.cache.OptimizationResult;
import org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper.InterpolatingProverWithAssumptionsWrapper;
import org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper.ProverWithAssumptionsWrapper;

import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public abstract class AbstractSolverContext implements SolverContext {

  private final FormulaManager fmgr;
  private final Map<OptimizationQuery, OptimizationResult> optimizationCache;
  private final SolverContextStatistics statistics;

  protected AbstractSolverContext(FormulaManager fmgr) {
    this.fmgr = fmgr;
    optimizationCache = new HashMap<>();
    statistics = new SolverContextStatistics();
  }

  @Override
  public final FormulaManager getFormulaManager() {
    return fmgr;
  }

  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    Set<ProverOptions> opts = EnumSet.noneOf(ProverOptions.class);
    Collections.addAll(opts, options);
    ProverEnvironment out = newProverEnvironment0(opts);
    if (!supportsAssumptionSolving()) {
      // In the case we do not already have a prover environment with assumptions,
      // we add a wrapper to it
      out = new ProverWithAssumptionsWrapper(out);
    }
    return out;
  }

  protected abstract ProverEnvironment newProverEnvironment0(Set<ProverOptions> options);

  @SuppressWarnings("resource")
  @Override
  public final InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation() {

    InterpolatingProverEnvironment<?> out = newProverEnvironmentWithInterpolation0();
    if (!supportsAssumptionSolving()) {
      // In the case we do not already have a prover environment with assumptions,
      // we add a wrapper to it
      out = new InterpolatingProverWithAssumptionsWrapper<>(out, fmgr);
    }
    return out;
  }

  protected abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0();

  /**
   * Whether the solver supports solving under some given assumptions
   * (with all corresponding features) by itself,
   * i.e., whether {@link ProverEnvironment#isUnsatWithAssumptions(java.util.Collection)} and
   * {@link InterpolatingProverEnvironment#isUnsatWithAssumptions(java.util.Collection)}
   * are fully implemented.
   *
   * <p>Otherwise, i.e., if this method returns {@code false}, the solver does not need to support
   * this feature and may simply {@code throw UnsupportedOperationException} in the respective
   * methods. This class will wrap the prover environments and provide an implementation of the
   * feature.
   *
   * <p>This method is expected to always return the same value.
   * Otherwise the behavior of this class is undefined.
   */
  protected abstract boolean supportsAssumptionSolving();

  @Override
  public final OptimizationProverEnvironment newCachedOptimizationProverEnvironment() {
    return new CachingOptimizationProverEnvironment(
        newOptimizationProverEnvironment(),
        optimizationCache,
        statistics.getOptimizationCacheStatistics());
  }

  @Override
  public SolverContextStatistics getStatistics() {
    return statistics;
  }
}
