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
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverlessFormulaCreator extends FormulaCreator<String, String, String,
    String> {
  protected SolverlessFormulaCreator(
      String pS,
      String boolType,
      @Nullable String pIntegerType,
      @Nullable String pRationalType,
      @Nullable String stringType,
      @Nullable String regexType) {
    super(pS, boolType, pIntegerType, pRationalType, stringType, regexType);
  }

  @Override
  public String getBitvectorType(int bitwidth) {
    return "";
  }

  @Override
  public String getFloatingPointType(FloatingPointType type) {
    return "";
  }

  @Override
  public String getArrayType(String indexType, String elementType) {
    return "";
  }

  @Override
  public String makeVariable(String pS, String varName) {
    return "";
  }

  @Override
  public FormulaType<?> getFormulaType(String formula) {
    return null;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, String f) {
    return null;
  }

  @Override
  public String callFunctionImpl(String declaration, List<String> args) {
    return "";
  }

  @Override
  public String declareUFImpl(String pName, String pReturnType, List<String> pArgTypes) {
    return "";
  }

  @Override
  protected String getBooleanVarDeclarationImpl(String pS) {
    return "";
  }
}
