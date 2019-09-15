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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exit;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_major_version;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_patch_level;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_version;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_init;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_config;

import java.util.Set;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public class Yices2SolverContext extends AbstractSolverContext {

  private final long yicesEnvironment;
  private final long yicesConfig;
  private final Yices2FormulaCreator creator;

  public Yices2SolverContext(
      FormulaManager pFmgr,
      long yicesConfig,
      long yicesEnvironment,
      Yices2FormulaCreator creator) {
    super(pFmgr);
    // TODO Auto-generated constructor stub
    this.yicesConfig = yicesConfig;
    this.yicesEnvironment = yicesEnvironment;
    this.creator = creator;
  }

  public static Yices2SolverContext create(NonLinearArithmetic pNonLinearArithmetic) {
    NativeLibraries.loadLibrary("yices2j");
    yices_init();
    long yicesConf = yices_new_config();
    yices_set_config(yicesConf, "solver-type", "dpllt");
    yices_set_config(yicesConf, "mode", "push-pop");
    // TODO SET OPTIONS
    // TODO SET LOGIC
    long yicesEnv = yices_new_context(yicesConf);
    // TODO Might not actually need yicesEnv
    Yices2FormulaCreator creator = new Yices2FormulaCreator(yicesEnv);

    Yices2UFManager functionTheory = new Yices2UFManager(creator);
    Yices2BooleanFormulaManager booleanTheory = new Yices2BooleanFormulaManager(creator);
    Yices2BitvectorFormulaManager bitvectorTheory = new Yices2BitvectorFormulaManager(creator);
    // TODO nonLinearArithmeticParam?
    Yices2IntegerFormulaManager integerTheory =
        new Yices2IntegerFormulaManager(creator, pNonLinearArithmetic);
    Yices2RationalFormulaManager rationalTheory =
        new Yices2RationalFormulaManager(creator, pNonLinearArithmetic);
    Yices2FormulaManager manager =
        new Yices2FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory);
    return new Yices2SolverContext(manager, yicesConf, yicesEnv, creator);
  }
  @Override
  public String getVersion() {
    String version = String.valueOf(yices_get_version());
    String majorVersion = String.valueOf(yices_get_major_version());
    String patchLevel = String.valueOf(yices_get_patch_level());
    String yicesVersion = version + "." + majorVersion + "." + patchLevel;
    return yicesVersion;
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.YICES2;
  }

  @Override
  public void close() {
    // TODO freeing context and config might not be needed
    yices_free_config(yicesConfig);
    yices_free_context(yicesEnvironment);
    yices_exit();
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    // TODO Auto-generated method stub
    return new Yices2TheoremProver(creator, pOptions);
  }

  @Override
  protected InterpolatingProverEnvironment<?>
      newProverEnvironmentWithInterpolation0(Set<ProverOptions> pSet) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected OptimizationProverEnvironment
      newOptimizationProverEnvironment0(Set<ProverOptions> pSet) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }

}
