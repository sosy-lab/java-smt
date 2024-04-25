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

package org.sosy_lab.java_smt.solvers.apron;

import apron.ApronException;
import apron.Environment;
import apron.Manager;
import apron.Polka;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronBooleanType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronIntegerType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;

public class ApronSolverContext extends AbstractSolverContext {

  private final ApronFormulaCreator formulaCreator;
  private final Manager manager;
  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private boolean closed = false;

  protected ApronSolverContext(
      ApronFormulaManager fmgr,
      Manager pManager,
      ApronFormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    super(fmgr);
    this.manager = pManager;
    this.formulaCreator = pFormulaCreator;
    this.logger = pLogger;
    this.shutdownNotifier = pShutdownNotifier;
  }

  public static synchronized ApronSolverContext create(
      NonLinearArithmetic pNonLinearArithmetic,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    Environment env = new Environment();
    Manager manager = new Polka(true);
    ApronBooleanType booleanType = new ApronBooleanType();
    ApronIntegerType integerType = new ApronIntegerType();
    ApronRationalType rationalType = new ApronRationalType();
    ApronFormulaCreator formulaCreator =
        new ApronFormulaCreator(manager, env, booleanType, integerType, rationalType);
    ApronUFManager ufManager = new ApronUFManager(formulaCreator);
    ApronBooleanFormulaManager booleanFormulaManager =
        new ApronBooleanFormulaManager(formulaCreator);
    ApronIntegerFormulaManager integerFormulaManager =
        new ApronIntegerFormulaManager(formulaCreator, pNonLinearArithmetic);
    ApronRationalFormulaManager rationalFormulaManager =
        new ApronRationalFormulaManager(formulaCreator, pNonLinearArithmetic);
    ApronFormulaManager fmgr =
        new ApronFormulaManager(
            formulaCreator,
            ufManager,
            booleanFormulaManager,
            integerFormulaManager,
            rationalFormulaManager);
    return new ApronSolverContext(fmgr, manager, formulaCreator, pShutdownNotifier, pLogger);
  }

  public Manager getManager() {
    return this.manager;
  }

  public ApronFormulaCreator getFormulaCreator() {
    return this.formulaCreator;
  }

  @Override
  public String getVersion() {
    return this.manager.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.APRON;
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
      logger.log(Level.FINER, "Freeing Apron Environment");
    }
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    return newApronProverEnvironment(options);
  }

  private ProverEnvironment newApronProverEnvironment(Set<ProverOptions> pProverOptions) {
    try {
      ApronBooleanFormulaManager booleanFormulaManager =
          new ApronBooleanFormulaManager(this.formulaCreator);
      return new ApronTheoremProver(
          pProverOptions, booleanFormulaManager, this.shutdownNotifier, this);
    } catch (ApronException pApronException) {
      throw new RuntimeException(pApronException);
    }
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Optimization prover not supported by Apron.");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }
}
