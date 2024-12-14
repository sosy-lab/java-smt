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

import java.util.Collection;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessBooleanFormulaManager extends AbstractBooleanFormulaManager<DummyFormula,
    FormulaTypesForChecking, DummyEnv, DummyFunction> {

  public SolverLessBooleanFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DummyFormula makeVariableImpl(String pVar) {
    DummyFormula result = new DummyFormula(FormulaTypesForChecking.BOOLEAN);
    result.setName(pVar);
    return result;
  }

  @Override
  protected DummyFormula makeBooleanImpl(boolean value) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula not(DummyFormula pParam1) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula and(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula or(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula xor(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula equivalence(DummyFormula bits1, DummyFormula bits2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected boolean isTrue(DummyFormula bits) {
    return true;
  }

  @Override
  protected boolean isFalse(DummyFormula bits) {
    return false;
  }

  @Override
  protected DummyFormula ifThenElse(DummyFormula cond, DummyFormula f1, DummyFormula f2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  public BooleanFormula makeBoolean(boolean value) {
    return super.makeBoolean(value);
  }
}

