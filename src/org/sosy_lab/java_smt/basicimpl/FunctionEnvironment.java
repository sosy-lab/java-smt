// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class FunctionEnvironment {

  Object result;
  List<Object> inputParams;
  Function<List<Object>, String> functionToString;
  Keyword expressionType;
  int bitVecLength;
  String ufName = "";
  String ufInputType = "";
  String ufOutputType = "";
  String arrayIndexType = "";
  String arrayValueType = "";

  protected FunctionEnvironment(
      Object pResult,
      List<Object> pInputParams,
      Function<List<Object>, String> pFunctionToString,
      Keyword pKeyword) {

    result = pResult;
    inputParams = pInputParams;
    functionToString = pFunctionToString;
    expressionType = pKeyword;
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

  public Keyword getExpressionType() {
    return expressionType;
  }

  public void setExpressionType(Keyword pExpressionType) {
    expressionType = pExpressionType;
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

  public Function<List<Object>, String> getFunctionToString() {
    return functionToString;
  }

  public void setFunctionToString(Function<List<Object>, String> pFunctionToString) {
    functionToString = pFunctionToString;
  }

  public void setArrayIndexType(String pArrayIndexType) {
    arrayIndexType = pArrayIndexType;
  }

  public void setArrayValueType(String pArrayValueType) {
    arrayValueType = pArrayValueType;
  }

  public String getUFName() {
    return ufName;
  }

  public void setUFName(String pUFName) {
    ufName = pUFName;
  }

  public String getArrayIndexType() {
    return arrayIndexType;
  }

  public String getArrayValueType() {
    return arrayValueType;
  }

  public String getUFInputType() {
    return ufInputType;
  }

  public void setUFInputType(String pUFInputType) {
    ufInputType = pUFInputType;
  }

  public String getUFOutputType() {
    return ufOutputType;
  }

  public void setUFOutputType(String pUFOutputType) {
    ufOutputType = pUFOutputType;
  }
}
