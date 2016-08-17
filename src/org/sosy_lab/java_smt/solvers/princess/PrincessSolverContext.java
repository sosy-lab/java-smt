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

package org.sosy_lab.java_smt.solvers.princess;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackInterpolatingProver;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackTheoremProver;

import java.util.Set;

import javax.annotation.Nullable;

public final class PrincessSolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.princess")
  static class PrincessOptions {
    @Option(
      secure = true,
      description =
          "The number of atoms a term has to have before"
              + " it gets abbreviated if there are more identical terms."
    )
    private int minAtomsForAbbreviation = 100;

    @Option(
      secure = true,
      description =
          "Princess needs to copy all symbols for each new prover. "
              + "This flag allows to reuse old unused provers and avoid the overhead."
    )
    // TODO someone should measure the overhead, perhaps it is negligible.
    private boolean reuseProvers = true;

    PrincessOptions(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }

    public int getMinAtomsForAbbreviation() {
      return minAtomsForAbbreviation;
    }

    boolean reuseProvers() {
      return reuseProvers;
    }
  }

  private final PrincessFormulaManager manager;
  private final PrincessFormulaCreator creator;

  private PrincessSolverContext(PrincessFormulaManager manager, PrincessFormulaCreator creator) {
    super(manager);
    this.manager = manager;
    this.creator = creator;
  }

  public static SolverContext create(
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pLogfileTemplate)
      throws InvalidConfigurationException {
    PrincessOptions options = new PrincessOptions(config);
    PrincessEnvironment env = new PrincessEnvironment(pLogfileTemplate, pShutdownNotifier, options);
    PrincessFormulaCreator creator =
        new PrincessFormulaCreator(env, PrincessTermType.Boolean, PrincessTermType.Integer);

    // Create managers
    PrincessUFManager functionTheory = new PrincessUFManager(creator);
    PrincessBooleanFormulaManager booleanTheory = new PrincessBooleanFormulaManager(creator);
    PrincessIntegerFormulaManager integerTheory = new PrincessIntegerFormulaManager(creator);
    PrincessArrayFormulaManager arrayTheory = new PrincessArrayFormulaManager(creator);
    PrincessQuantifiedFormulaManager quantifierTheory =
        new PrincessQuantifiedFormulaManager(creator);
    PrincessFormulaManager manager =
        new PrincessFormulaManager(
            creator, functionTheory, booleanTheory, integerTheory, arrayTheory, quantifierTheory);
    return new PrincessSolverContext(manager, creator);
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    if (options.contains(ProverOptions.GENERATE_UNSAT_CORE)
        || options.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      throw new UnsupportedOperationException("Princess does not support unsat core generation");
    }
    return new ReusableStackTheoremProver(
        (PrincessTheoremProver) creator.getEnv().getNewProver(false, manager, creator));
  }

  @SuppressWarnings("resource")
  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0() {
    return new ReusableStackInterpolatingProver<>(
        (PrincessInterpolatingProver) creator.getEnv().getNewProver(true, manager, creator));
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment() {
    throw new UnsupportedOperationException("Princess does not support optimization");
  }

  @Override
  public String getVersion() {
    return creator.getEnv().getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.PRINCESS;
  }

  @Override
  public void close() {}

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
