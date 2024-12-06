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
package org.sosy_lab.java_smt.solvers.Solverless;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.Solverless.SolverlessFormula;

public class SolverLessBooleanFormulaManager extends AbstractBooleanFormulaManager<SolverlessFormula,
    SolverlessFormula, SolverlessFormula, SolverlessFormula> {

  @Override
  protected SolverLessFormula makeVariableImpl(String pVarName) {
    return new SolverLessFormula("BoolVar: " + pVarName);
  }

  @Override
  protected SolverLessFormula makeBooleanImpl(boolean value) {
    return new SolverLessFormula("BoolValue: " + value);
  }

  @Override
  protected SolverlessFormula equivalence(Object bits1, Object bits2) {
    return null;
  }

  @Override
  protected SolverlessFormula or(Object pParam1, Object pParam2) {
    return null;
  }

  @Override
  protected SolverlessFormula and(Object pParam1, Object pParam2) {
    return null;
  }

  @Override
  protected SolverlessFormula not(Object pParam1) {
    return null;
  }

  @Override
  protected SolverLessFormula not(SolverLessFormula pParam) {
    return new SolverLessFormula("NOT(" + pParam + ")");
  }

  @Override
  protected SolverLessFormula and(SolverLessFormula pParam1, SolverLessFormula pParam2) {
    return new SolverLessFormula("AND(" + pParam1 + ", " + pParam2 + ")");
  }

  @Override
  protected SolverLessFormula or(SolverLessFormula pParam1, SolverLessFormula pParam2) {
    return new SolverLessFormula("OR(" + pParam1 + ", " + pParam2 + ")");
  }

  @Override
  protected SolverLessFormula xor(Object pParam1, Object pParam2) {
    return null;
  }

  @Override
  protected SolverLessFormula equivalence(SolverLessFormula pParam1, SolverLessFormula pParam2) {
    return new SolverLessFormula("EQ(" + pParam1 + ", " + pParam2 + ")");
  }

  @Override
  protected SolverLessFormula ifThenElse(Object cond, Object f1, Object f2) {
    return null;
  }

  @Override
  protected boolean isFalse(Object bits) {
    return false;
  }

  @Override
  protected boolean isTrue(Object bits) {
    return false;
  }

  @Override
  public BooleanFormula makeBoolean(boolean value) {
    return super.makeBoolean(value);
  }
}

