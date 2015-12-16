/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.common.Appender;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.OptEnvironment;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import javax.annotation.Nullable;

public class CVC4FormulaManager extends AbstractFormulaManager<Expr, Type, CVC4Environment> {

  private CVC4FormulaManager(
      FormulaCreator<Expr, Type, CVC4Environment> pFormulaCreator,
      CVC4UnsafeFormulaManager pUfmgr,
      CVC4FunctionFormulaManager pFfmgr,
      CVC4BooleanFormulaManager pBfmgr,
      CVC4IntegerFormulaManager pIfmgr) {
    super(pFormulaCreator, pUfmgr, pFfmgr, pBfmgr, pIfmgr, null, null, null, null, null);
  }

  @SuppressWarnings("unused")
  public static CVC4FormulaManager create(
      LogManager logger,
      Configuration config,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogFile,
      long randomSeed)
      throws InvalidConfigurationException {

    // Init CVC4
    NativeLibraries.loadLibrary("cvc4jni");

    edu.nyu.acsys.CVC4.Options cvc4options = new edu.nyu.acsys.CVC4.Options();
    // TODO set randomseed, furtherOptions

    final CVC4Environment env = new CVC4Environment(cvc4options);

    // Create CVC4FormulaCreator
    CVC4FormulaCreator creator = new CVC4FormulaCreator(env);

    // Create managers
    CVC4UnsafeFormulaManager ufmgr = new CVC4UnsafeFormulaManager(creator);
    CVC4FunctionFormulaManager ffmgr = new CVC4FunctionFormulaManager(creator);
    CVC4BooleanFormulaManager bfmgr = new CVC4BooleanFormulaManager(creator, ufmgr);
    CVC4IntegerFormulaManager ifmgr = new CVC4IntegerFormulaManager(creator);

    return new CVC4FormulaManager(creator, ufmgr, ffmgr, bfmgr, ifmgr);
  }

  BooleanFormula encapsulateBooleanFormula(Expr t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public ProverEnvironment newProverEnvironment(
      boolean pGenerateModels, boolean pGenerateUnsatCore) {
    return new CVC4TheoremProver(this);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(boolean pShared) {
    throw new UnsupportedOperationException("CVC4 does not support interpolation.");
  }

  @Override
  public OptEnvironment newOptEnvironment() {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException();
  }

  @Override
  public String getVersion() {
    return "CVC4 " + CVC4JNI.Configuration_getVersionString();
  }

  @Override
  public Appender dumpFormula(Expr pT) {
    throw new UnsupportedOperationException();
  }
}
