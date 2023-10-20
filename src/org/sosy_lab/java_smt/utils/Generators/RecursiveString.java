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

package org.sosy_lab.java_smt.utils.Generators;

import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

public class RecursiveString <TI extends Formula, TE extends Formula> {

  Object result;
  List<Object> inputParams;
  Function<List<Object>, String> saveResult;
  String variableType;
  int bitVecLength;
  String UFName;
  String UFInputType;
  String UFOutputType;
  String ArrayIndexType;
  String ArrayValueType;


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

  public int getBitVecLength() {
    return bitVecLength;
  }

  public void setBitVecLength(int pBitVecLength) {
    bitVecLength = pBitVecLength;
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

  public void setArrayIndexType(String pArrayIndexType) {
    ArrayIndexType = pArrayIndexType;
  }

  public void setArrayValueType(String pArrayValueType) {
    ArrayValueType = pArrayValueType;
  }

  public String getUFName() {
    return UFName;
  }

  public void setUFName(String pUFName) {
    UFName = pUFName;
  }

  public String getArrayIndexType() {
    return ArrayIndexType;
  }

  public String getArrayValueType() {
    return ArrayValueType;
  }

  public String getUFInputType() {
    return UFInputType;
  }

  public void setUFInputType(String pUFInputType) {
    UFInputType = pUFInputType;
  }

  public String getUFOutputType() {
    return UFOutputType;
  }

  public void setUFOutputType(String pUFOutputType) {
    UFOutputType = pUFOutputType;
  }

  @Override
  public String toString() {
    return "RecursiveString{" +
        "result=" + result +
        ", inputParams=" + inputParams +
        ", saveResult=" + saveResult +
        ", variableType='" + variableType + '\'' +
        ", bitVecLength=" + bitVecLength +
        ", ArrayIndexType=" + ArrayIndexType +
        ", ArrayValueType=" + ArrayValueType +
        '}';
  }
}
