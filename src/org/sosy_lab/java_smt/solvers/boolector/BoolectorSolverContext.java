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
package org.sosy_lab.java_smt.solvers.boolector;

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
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.reusableStack.ReusableStackTheoremProver;

public final class BoolectorSolverContext extends AbstractSolverContext {

  private final BoolectorFormulaManager manager;
  private final BoolectorFormulaCreator creator;

  protected BoolectorSolverContext(
      BoolectorFormulaManager manager,
      BoolectorFormulaCreator creator) {
    super(manager);
    this.manager = manager;
    this.creator = creator;
  }

  public static BoolectorSolverContext create(
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed)
      throws InvalidConfigurationException {

    BoolectorEnvironment env =
        new BoolectorEnvironment(config, solverLogfile, pShutdownNotifier, (int) randomSeed);
    BoolectorFormulaCreator creator = new BoolectorFormulaCreator(env);

    BoolectorUFManager functionTheory = new BoolectorUFManager(creator);
    BoolectorBooleanFormulaManager booleanTheory = new BoolectorBooleanFormulaManager(creator);
    BoolectorBitvectorFormulaManager bitvectorTheory =
        new BoolectorBitvectorFormulaManager(creator);
    BoolectorQuantifiedFormulaManager quantifierTheory =
        new BoolectorQuantifiedFormulaManager(creator);
    BoolectorArrayFormulaManager arrayTheory = new BoolectorArrayFormulaManager(creator);
    BoolectorFormulaManager manager =
        new BoolectorFormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            bitvectorTheory,
            quantifierTheory,
            arrayTheory);
    return new BoolectorSolverContext(manager, creator);
  }

  @Override
  public String getVersion() {
    return BtorJNI.boolector_version(creator.getEnv().getBtor());
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.BOOLECTOR;
  }

  @Override
  public void close() {
    // Problem: Cloning results in not beeing able to access var with old name (string)
    // NOT Cloning results in murdering btor that is still beeing used
    // BtorJNI.boolector_delete(creator.getEnv().getBtor());
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new ReusableStackTheoremProver(
        (BoolectorTheoremProver) creator.getEnv().getNewProver(manager, creator, pOptions));
  }

  @Override
  protected InterpolatingProverEnvironment<?>
      newProverEnvironmentWithInterpolation0(Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Boolector does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment
      newOptimizationProverEnvironment0(Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Boolector does not support optimization");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }
}
