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
package org.sosy_lab.java_smt.solvers.wrapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.wrapper.caching.CachingEnvironmentWrapper;
import org.sosy_lab.java_smt.solvers.wrapper.caching.CachingInterpolatingEnvironmentWrapper;
import org.sosy_lab.java_smt.solvers.wrapper.caching.CachingOptimizationEnvironmentWrapper;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache.CachingMode;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingEnvironmentWrapper;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingInterpolatingEnvironmentWrapper;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingOptimizationEnvironmentWrapper;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategies;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class WrapperSolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.wrapper")
  private static class WrapperOptions {
    @Option(secure = true, description = "Which SMT solver to use as delegate.")
    public Solvers solver = Solvers.SMTINTERPOL;

    @Option(
      secure = true,
      description = "If formulas should be canonized before queried to the solver."
    )
    public boolean canonize = false;

    @Option(secure = true, description = "Which strategies to use for canonization")
    public Set<CanonizingStrategies> strategies = null;

    @Option(secure = true, description = "If answers of solvers should be cached.")
    public boolean cache = false;
  }

  private SolverContext delegate;
  private WrapperOptions options;

  public WrapperSolverContext(
      FormulaManager pFmgr, SolverContext pDelegate, WrapperOptions pOptions) {
    super(pFmgr);
    delegate = pDelegate;
    options = pOptions;
  }

  @SuppressWarnings("resource")
  public static SolverContext create(
      Configuration pConfig, SolverContextFactory pSolverContextFactory)
      throws InvalidConfigurationException {
    WrapperOptions options = new WrapperOptions();
    pConfig.inject(options);
    SolverContext delegate = pSolverContextFactory.generateContext(options.solver);
    return new WrapperSolverContext(delegate.getFormulaManager(), delegate, options);
  }

  @Override
  public String getVersion() {
    return delegate.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return delegate.getSolverName();
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    ProverEnvironment env = delegate.newProverEnvironment(pOptions.toArray(new ProverOptions[] {}));

    if (options.cache) {
      // FIXME: Parameterize CachingMode
      env = new CachingEnvironmentWrapper(env, delegate.getFormulaManager(), CachingMode.IN_MEMORY);
    }

    if (options.canonize) {
      List<CanonizingStrategy> strategies = organizeStrategies();
      env = new CanonizingEnvironmentWrapper(env, delegate.getFormulaManager(), strategies);
    }

    return env;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    InterpolatingProverEnvironment<?> env =
        delegate.newProverEnvironmentWithInterpolation(pSet.toArray(new ProverOptions[] {}));

    if (options.cache) {
      // FIXME: Parameterize CachingMode
      env =
          new CachingInterpolatingEnvironmentWrapper<>(
              env,
              delegate.getFormulaManager(),
              CachingMode.IN_MEMORY);
    }

    if (options.canonize) {
      List<CanonizingStrategy> strategies = organizeStrategies();
      env =
          new CanonizingInterpolatingEnvironmentWrapper<>(
              env,
              delegate.getFormulaManager(),
              strategies);
    }

    return env;
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    OptimizationProverEnvironment env =
        delegate.newOptimizationProverEnvironment(pSet.toArray(new ProverOptions[] {}));

    if (options.cache) {
      // FIXME: Parameterize CachingMode
      env =
          new CachingOptimizationEnvironmentWrapper(
              env,
              delegate.getFormulaManager(),
              CachingMode.IN_MEMORY);
    }

    if (options.canonize) {
      List<CanonizingStrategy> strategies = organizeStrategies();
      env =
          new CanonizingOptimizationEnvironmentWrapper(
              env,
              delegate.getFormulaManager(),
              strategies);
    }

    return env;
  }

  private List<CanonizingStrategy> organizeStrategies() {
    List<CanonizingStrategy> strategies = new ArrayList<>();
    if (options.strategies != null) {
      strategies =
          options.strategies.stream()
              .sorted((s0, s1) -> s0.getPriority() - s1.getPriority())
              .map(CanonizingStrategies::getStrategy)
              .collect(Collectors.toList());

    }
    if (strategies.isEmpty()) {
      strategies.add(CanonizingStrategies.IDENTITY.getStrategy());
    }
    return strategies;
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    // Avoid additional wrapping
    return true;
  }
}
