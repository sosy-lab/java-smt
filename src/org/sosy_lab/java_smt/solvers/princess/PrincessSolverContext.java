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

import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackInterpolatingProver;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackTheoremProver;

public final class PrincessSolverContext extends AbstractSolverContext {

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
      @Nullable PathCounterTemplate pLogfileTemplate,
      int pRandomSeed,
      NonLinearArithmetic pNonLinearArithmetic)
      throws InvalidConfigurationException {
    PrincessEnvironment env =
        new PrincessEnvironment(config, pLogfileTemplate, pShutdownNotifier, pRandomSeed);
    PrincessFormulaCreator creator = new PrincessFormulaCreator(env);

    // Create managers
    PrincessUFManager functionTheory = new PrincessUFManager(creator);
    PrincessBooleanFormulaManager booleanTheory = new PrincessBooleanFormulaManager(creator);
    PrincessIntegerFormulaManager integerTheory =
        new PrincessIntegerFormulaManager(creator, pNonLinearArithmetic);
    PrincessBitvectorFormulaManager bitvectorTheory = new PrincessBitvectorFormulaManager(creator);
    PrincessArrayFormulaManager arrayTheory = new PrincessArrayFormulaManager(creator);
    PrincessQuantifiedFormulaManager quantifierTheory =
        new PrincessQuantifiedFormulaManager(creator);
    PrincessFormulaManager manager =
        new PrincessFormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            bitvectorTheory,
            arrayTheory,
            quantifierTheory);
    return new PrincessSolverContext(manager, creator);
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    if (options.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      throw new UnsupportedOperationException(
          "Princess does not support unsat core generation with assumptions yet");
    }
    return new ReusableStackTheoremProver(
        (PrincessTheoremProver) creator.getEnv().getNewProver(false, manager, creator, options));
  }

  @SuppressWarnings("resource")
  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    return new ReusableStackInterpolatingProver<>(
        (PrincessInterpolatingProver)
            creator.getEnv().getNewProver(true, manager, creator, options));
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> options) {
    throw new UnsupportedOperationException("Princess does not support optimization");
  }

  @Override
  public String getVersion() {
    return "Princess (" + ap.SimpleAPI.version() + ")";
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
