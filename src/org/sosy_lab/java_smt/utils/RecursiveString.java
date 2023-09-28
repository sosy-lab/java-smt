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

package org.sosy_lab.java_smt.utils;

import java.util.List;
import java.util.function.Function;

public class RecursiveString {

  Object result;
  List<Object> inputParams;
  Function<List<Object>, String> saveResult;

  String variableType;

  public RecursiveString(
      Object pResult,
      List<Object> pInputParams,
      Function<List<Object>, String> pSaveResult, String pVariableType) {
    result = pResult;
    inputParams = pInputParams;
    saveResult = pSaveResult;
    variableType = pVariableType;
  }

  public Object getResult() {
    return result;
  }

  public String getVariableType() {
    return variableType;
  }

  public void setVariableType(String pVariableType) {
    variableType = pVariableType;
  }

  public void setResult(Object pResult) {
    result = pResult;
  }

  public List<Object> getInputParams() {
    return inputParams;
  }

  public void setInputParams(List<Object> pInputParams) {
    inputParams = pInputParams;
  }

  public Function<List<Object>, String> getSaveResult() {
    return saveResult;
  }

  public void setSaveResult(Function<List<Object>, String> pSaveResult) {
    saveResult = pSaveResult;
  }
}
