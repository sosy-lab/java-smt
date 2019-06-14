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
package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;
import edu.nyu.acsys.CVC4.ExprManager;
import java.util.Set;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class CVC4SolverContext extends AbstractSolverContext {

  // creator is final, except after closing, then null.
  private CVC4FormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  private final int randomSeed;

  private CVC4SolverContext(
      CVC4FormulaCreator creator,
      CVC4FormulaManager manager,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed) {
    super(manager);
    this.creator = creator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
  }

  public static SolverContext create(
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      ShutdownNotifier pShutdownNotifier) {

    NativeLibraries.loadLibrary("cvc4jni");

    // ExprManager is the central class for creating expressions/terms/formulae.
    ExprManager exprManager = new ExprManager();
    CVC4FormulaCreator creator = new CVC4FormulaCreator(exprManager);

    // Create managers
    CVC4UFManager functionTheory = new CVC4UFManager(creator);
    CVC4BooleanFormulaManager booleanTheory = new CVC4BooleanFormulaManager(creator);
    CVC4IntegerFormulaManager integerTheory =
        new CVC4IntegerFormulaManager(creator, pNonLinearArithmetic);
    CVC4RationalFormulaManager rationalTheory =
        new CVC4RationalFormulaManager(creator, pNonLinearArithmetic);
    CVC4BitvectorFormulaManager bitvectorTheory = new CVC4BitvectorFormulaManager(creator);
    CVC4ArrayFormulaManager arrayTheory = new CVC4ArrayFormulaManager(creator);
    CVC4SLFormulaManager slTheory = new CVC4SLFormulaManager(creator);
    CVC4FormulaManager manager =
        new CVC4FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            arrayTheory,
            slTheory);

    return new CVC4SolverContext(creator, manager, pShutdownNotifier, randomSeed);
  }

  @Override
  public String getVersion() {
    return "CVC4 " + CVC4JNI.Configuration_getVersionString();
  }

  @Override
  public void close() {
    if (creator != null) {
      creator.getEnv().delete();
      creator = null;
    }
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC4;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new CVC4TheoremProver(creator, shutdownNotifier, randomSeed, pOptions);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC4 does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC4 does not support optimization");
  }
}
