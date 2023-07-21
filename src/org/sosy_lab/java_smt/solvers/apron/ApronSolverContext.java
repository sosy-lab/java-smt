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
import apron.Box;
import apron.Environment;
import apron.Manager;
import com.microsoft.z3.Native;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronBooleanType;

public class ApronSolverContext extends AbstractSolverContext {

  private Manager manager;
  private final ApronFormulaCreator formulaCreator;
  protected ShutdownNotifier shutdownNotifier;
  protected ApronSolverContext(ApronFormulaManager fmgr,
                               Manager pManager,
                               ApronFormulaCreator pFormulaCreator,
                               ShutdownNotifier pShutdownNotifier) {
    super(fmgr);
    this.manager = pManager;
    this.formulaCreator = pFormulaCreator;
    this.shutdownNotifier = pShutdownNotifier;
  }

  public static synchronized ApronSolverContext create(NonLinearArithmetic pNonLinearArithmetic,
                                                       ShutdownNotifier pShutdownNotifier){

    Environment env = new Environment();
    Manager manager = new Box();
    ApronBooleanType booleanType = new ApronBooleanType();
    ApronFormulaCreator formulaCreator = new ApronFormulaCreator(env, booleanType, null,null,null,null);
    ApronUFManager ufManager = new ApronUFManager(formulaCreator);
    ApronBooleanFormulaManager booleanFormulaManager =
        new ApronBooleanFormulaManager(formulaCreator);
    ApronIntegerFormulaManager integerFormulaManager =
        new ApronIntegerFormulaManager(formulaCreator, pNonLinearArithmetic);
    ApronRationalFormulaManager rationalFormulaManager =
        new ApronRationalFormulaManager(formulaCreator, pNonLinearArithmetic);
    ApronFormulaManager fmgr = new ApronFormulaManager(formulaCreator, ufManager,
        booleanFormulaManager,integerFormulaManager,rationalFormulaManager,null,null,null,null,
        null,null,null);
    return new ApronSolverContext(fmgr, manager, formulaCreator, pShutdownNotifier);
  }

  public Manager getManager(){
    return this.manager;
  }

  public ApronFormulaCreator getFormulaCreator(){
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
    //TODO
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    return newApronProverEnvironment(options);
  }

  private ProverEnvironment newApronProverEnvironment(Set<ProverOptions> pProverOptions){
    try{
      ApronBooleanFormulaManager booleanFormulaManager =
          new ApronBooleanFormulaManager(this.formulaCreator);
      return new ApronTheoremProver(pProverOptions,booleanFormulaManager,this.shutdownNotifier,this);
    } catch(ApronException pApronException){
      System.out.println(pApronException.toString());
      System.exit(0);
      return null;
    }
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(Set<ProverOptions> pSet) {
    return null;
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(Set<ProverOptions> pSet) {
    return null;
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
