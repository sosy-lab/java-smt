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

package org.sosy_lab.java_smt.solvers.dreal4;

import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.*;

import java.util.Set;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public class DReal4SolverContext extends AbstractSolverContext {

  private final DReal4FormulaManager manager;
  private final DReal4FormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  public DReal4SolverContext(
      DReal4FormulaManager pManager, DReal4FormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pManager);
    manager = pManager;
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
  }

  public static DReal4SolverContext create(
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader
      ) {

    pLoader.accept("dreal4");

    // Create config
    Config config = new Config();
    config.mutable_random_seed(randomSeed);

    DReal4FormulaCreator creator = new DReal4FormulaCreator(config);

    // Create manager
    DReal4UFManager functionTheory = new DReal4UFManager(creator);
    DReal4BooleanFormulaManager booleanTheory = new DReal4BooleanFormulaManager(creator);
    DReal4IntegerFormulaManager integerTheory = new DReal4IntegerFormulaManager(creator,
        pNonLinearArithmetic);
    DReal4RationalFormulaManager rationalTheory = new DReal4RationalFormulaManager(creator,
        pNonLinearArithmetic);
    DReal4QuantifiedFormulaManager quantifierTheory = new DReal4QuantifiedFormulaManager(creator);
    DReal4FormulaManager manager = new DReal4FormulaManager(creator, functionTheory,
        booleanTheory, integerTheory, rationalTheory, quantifierTheory);
    return new DReal4SolverContext(manager, creator, pShutdownNotifier);

  }
  @Override
  public String getVersion() {
    return "dReal " + drealJNI.Context_version();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.DREAL4;
  }

  @Override
  public void close() {}

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new DReal4TheoremProver(creator, pOptions, manager, shutdownNotifier);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("dReal does not support interpolation.");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("dReal does not support optimization.");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
