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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache.CachingMode;

public class CachingInterpolatingEnvironmentWrapper<T> extends AbstractCachingEnvironment<T>
    implements InterpolatingProverEnvironment<T> {

  private InterpolatingProverEnvironment<T> delegate;

  public CachingInterpolatingEnvironmentWrapper(
      InterpolatingProverEnvironment<T> pEnv,
      FormulaManager pMgr,
      CachingMode pMode,
      Configuration config,
      boolean solversFormulasCacheable)
      throws InvalidConfigurationException {
    super(pMgr, pMode, config, solversFormulasCacheable);
    delegate = pEnv;
  }

  @Override
  protected InterpolatingProverEnvironment<T> getDelegate() {
    return delegate;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    Formula translated = fromFormula(formula);
    Formula cached = cache.getFormulaInterpolant(translated, pFormulasOfA);
    BooleanFormula computed;
    if (cached == null) {
      assert delegate.isUnsat();
      computed = delegate.getInterpolant(pFormulasOfA);
      cached = fromFormula(computed);
      cache.storeFormulaInterpolant(translated, cached, pFormulasOfA);
    } else {
      computed = toFormula(cached);
    }
    return computed;
  }

  @Override
  public List<BooleanFormula>
      getTreeInterpolants(List<? extends Collection<T>> pPartitionedFormulas, int[] pStartOfSubTree)
          throws SolverException, InterruptedException {
    Formula translated = fromFormula(formula);
    List<BooleanFormula> computed = new ArrayList<>();
    List<Formula> cached =
        cache.getFormulaTreeInterpolants(translated, pPartitionedFormulas, pStartOfSubTree);
    if (cached == null) {
      assert delegate.isUnsat();
      computed =
          delegate
              .getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
      cached = computed.stream().map(f -> fromFormula(f)).collect(Collectors.toList());
      cache.storeFormulaTreeInterpolants(translated, cached, pPartitionedFormulas, pStartOfSubTree);
    } else {
      computed = cached.stream().map(f -> toFormula(f)).collect(Collectors.toList());
    }
    return computed;
  }
}
