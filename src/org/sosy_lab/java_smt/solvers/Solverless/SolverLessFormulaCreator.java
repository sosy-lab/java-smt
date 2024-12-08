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
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverLessFormulaCreator
    extends FormulaCreator<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  public SolverLessFormulaCreator() {
    super(new DummyEnv(), new DummyType(), new DummyType(), new DummyType(),
        new DummyType(),
        new DummyType());
  }

  @Override
  public DummyType getBitvectorType(int bitwidth) {
    return null;
  }

  @Override
  public DummyType getFloatingPointType(FloatingPointType type) {
    return null;
  }

  @Override
  public DummyType getArrayType(DummyType indexType, DummyType elementType) {
    return null;
  }

  @Override
  public DummyFormula makeVariable(DummyType pDummyType, String varName) {
    return null;
  }

  @Override
  public FormulaType<?> getFormulaType(DummyFormula formula) {
    return null;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DummyFormula f) {
    return null;
  }

  @Override
  public DummyFormula callFunctionImpl(DummyFunction declaration, List<DummyFormula> args) {
    return null;
  }

  @Override
  public DummyFunction declareUFImpl(
      String pName,
      DummyType pReturnType,
      List<DummyType> pArgTypes) {
    return null;
  }

  @Override
  protected DummyFunction getBooleanVarDeclarationImpl(DummyFormula pDummyFormula) {
    return null;
  }
}
