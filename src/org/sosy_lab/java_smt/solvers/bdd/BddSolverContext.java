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
package org.sosy_lab.java_smt.solvers.bdd;


import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.bdd.BddSort.BddBooleanSort;


public final class BddSolverContext extends AbstractSolverContext {


  private final BddFormulaManager manager;
  private final BddFormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  private final LogManager logger;

  private BddSolverContext(
      LogManager logger,
      FormulaManager manager,
      BddFormulaCreator creator,
      ShutdownNotifier shutdownNotifier) {
    super(manager);
    this.manager = (BddFormulaManager) manager;
    this.creator = creator;
    this.shutdownNotifier = shutdownNotifier;
    this.logger = logger;
  }

  public static BddSolverContext create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier
  )
      throws InvalidConfigurationException {
    RegionManager nestedRmgr = new JavaBDDRegionManager("java", config, logger);
    NamedRegionManager rmgr = new NamedRegionManager(nestedRmgr);
    BddFormulaCreator creator = new BddFormulaCreator(rmgr, BddBooleanSort.getInstance());
    BddBooleanFormulaManager bfmgr = new BddBooleanFormulaManager(creator);
    BddUFManager ufmgr = new BddUFManager(creator);
    FormulaManager fmgr = new BddFormulaManager(creator, bfmgr, ufmgr);
    return new BddSolverContext(logger, fmgr, creator, pShutdownNotifier);
}


  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    Set<ProverOptions> pOptions = null;
    return new BddTheoremProver(this, shutdownNotifier, creator, pOptions);
  }

  @Override
  protected OptimizationProverEnvironment
      newOptimizationProverEnvironment0(Set<ProverOptions> pSet) {
    Set<ProverOptions> pOptions = null;
    throw new UnsupportedOperationException();
  }

  @SuppressWarnings("unchecked")
  @Override
  protected InterpolatingProverEnvironment<?>
      newProverEnvironmentWithInterpolation0(Set<ProverOptions> pSet) {
    Set<ProverOptions> pOptions = null;
    throw new UnsupportedOperationException();
  }

  @Override
  public String getVersion() {
    return "Bdd (" + ap.SimpleAPI.version() + ")";
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.BDD;
  }

  @Override
  public void close() {}

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }


}
