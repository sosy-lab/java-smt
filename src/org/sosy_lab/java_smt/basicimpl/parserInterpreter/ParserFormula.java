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

package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.FormulaType;

public class ParserFormula {

  @Nullable String type;
  Object javaSmt;

  @Nullable FormulaType<?> returnType;

  @Nullable List<FormulaType<?>> inputParams;

  public ParserFormula(Object pJavaSmt) {
    javaSmt = pJavaSmt;
  }

  @Nullable
  public String getType() {
    return type;
  }

  public void setType(String pType) {
    type = pType;
  }

  public Object getJavaSmt() {
    return javaSmt;
  }

  public void setJavaSmt(Object pJavaSmt) {
    javaSmt = pJavaSmt;
  }

  @Nullable
  public FormulaType<?> getReturnType() {
    return returnType;
  }

  public void setReturnType(FormulaType<?> pReturnType) {
    returnType = pReturnType;
  }

  @Nullable
  public List<FormulaType<?>> getInputParams() {
    return inputParams;
  }

  public void setInputParams(List<FormulaType<?>> pInputParams) {
    inputParams = pInputParams;
  }
}
