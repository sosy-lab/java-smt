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

package org.sosy_lab.java_smt.solvers.smtinterpol;

import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackInterpolatingProver;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackTheoremProver;

public final class SmtInterpolSolverContext extends AbstractSolverContext {

  private final SmtInterpolEnvironment environment;
  private final SmtInterpolFormulaManager manager;

  private SmtInterpolSolverContext(
      SmtInterpolFormulaCreator pFormulaCreator, SmtInterpolFormulaManager pManager) {
    super(pManager);
    environment = pFormulaCreator.getEnv();
    manager = pManager;
  }

  public static SmtInterpolSolverContext create(
      Configuration config,
      LogManager logger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate smtLogfile,
      long randomSeed,
      NonLinearArithmetic pNonLinearArithmetic)
      throws InvalidConfigurationException {
    SmtInterpolEnvironment env =
        new SmtInterpolEnvironment(config, logger, pShutdownNotifier, smtLogfile, randomSeed);
    SmtInterpolFormulaCreator creator = new SmtInterpolFormulaCreator(env);
    SmtInterpolUFManager functionTheory = new SmtInterpolUFManager(creator);
    SmtInterpolBooleanFormulaManager booleanTheory =
        new SmtInterpolBooleanFormulaManager(creator, env.getTheory());
    SmtInterpolIntegerFormulaManager integerTheory =
        new SmtInterpolIntegerFormulaManager(creator, pNonLinearArithmetic);
    SmtInterpolRationalFormulaManager rationalTheory =
        new SmtInterpolRationalFormulaManager(creator, pNonLinearArithmetic);
    SmtInterpolArrayFormulaManager arrayTheory = new SmtInterpolArrayFormulaManager(creator);
    SmtInterpolFormulaManager manager =
        new SmtInterpolFormulaManager(
            creator, functionTheory, booleanTheory, integerTheory, rationalTheory, arrayTheory);
    return new SmtInterpolSolverContext(creator, manager);
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    return new ReusableStackTheoremProver(new SmtInterpolTheoremProver(manager, options));
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    return new ReusableStackInterpolatingProver<>(environment.getInterpolator(manager, options));
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> options) {
    throw new UnsupportedOperationException("SMTInterpol does not support optimization");
  }

  @Override
  public String getVersion() {
    return environment.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.SMTINTERPOL;
  }

  @Override
  public void close() {}

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
