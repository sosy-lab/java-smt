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

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;


public class DReal4FormulaCreator extends FormulaCreator<DRealTerm, Type, Context,
    DRealTerm> {

  public DReal4FormulaCreator(Context context) {
    super(context, Type.BOOLEAN, Type.INTEGER, Type.CONTINUOUS, null, null);
  }

  @Override
  public Type getBitvectorType(int bitwidth) {
    return null;
  }

  @Override
  public Type getFloatingPointType(FloatingPointType type) {
    return null;
  }

  @Override
  public Type getArrayType(Type indexType, Type elementType) {
    return null;
  }

  @Override
  public DRealTerm makeVariable(Type pType, String varName) {
    return new DRealTerm(new Variable(varName, pType), null, null);
  }

  @Override
  public FormulaType<?> getFormulaType(DRealTerm formula) {
    return null;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DRealTerm f) {
    return null;
  }

  @Override
  public DRealTerm callFunctionImpl(DRealTerm declaration, List<DRealTerm> args) {
    return null;
  }

  @Override
  public DRealTerm declareUFImpl(String pName, Type pReturnType, List<Type> pArgTypes) {
    return null;
  }

  @Override
  protected DRealTerm getBooleanVarDeclarationImpl(DRealTerm pDRealTerm) {
    return null;
  }
}
