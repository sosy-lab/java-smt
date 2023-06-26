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

import java.util.List;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class ApronFormulaCreator extends FormulaCreator {
  protected ApronFormulaCreator(
      Object pO,
      Object boolType,
      @Nullable Object pIntegerType,
      @Nullable Object pRationalType,
      @Nullable Object stringType,
      @Nullable Object regexType) {
    super(pO, boolType, pIntegerType, pRationalType, stringType, regexType);
  }

  @Override
  public Object getBitvectorType(int bitwidth) {
    return null;
  }

  @Override
  public Object getFloatingPointType(FloatingPointType type) {
    return null;
  }

  @Override
  public Object getArrayType(Object indexType, Object elementType) {
    return null;
  }

  @Override
  public Object makeVariable(Object pO, String varName) {
    return null;
  }

  @Override
  public FormulaType<?> getFormulaType(Object formula) {
    return null;
  }

  @Override
  public Object callFunctionImpl(Object declaration, List args) {
    return null;
  }

  @Override
  public Object declareUFImpl(String pName, Object pReturnType, List pArgTypes) {
    return null;
  }

  @Override
  protected Object getBooleanVarDeclarationImpl(Object pO) {
    return null;
  }

  @Override
  public Object visit(FormulaVisitor visitor, Formula formula, Object f) {
    return null;
  }
}
