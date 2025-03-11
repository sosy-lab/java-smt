// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

// TODO Use AutoValue
// TODO Can we make this typesafe?
public class FunctionEnvironment {

  Object result;
  List<Object> inputParams;
  Function<List<Object>, String> functionToString;
  Keyword expressionType;
  int bitVecLength;
  int floatingPointMantissa;
  int floatingPointExponent;
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
    Generator.throwExceptionWhenParameterIsNull(
        List.of(pResult, pInputParams, pFunctionToString, pKeyword));
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
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pExpressionType));
    expressionType = pExpressionType;
  }

  public void setResult(Object pResult) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pResult));
    result = pResult;
  }

  public List<Object> getInputParams() {
    return inputParams;
  }

  public void setInputParams(List<Object> pInputParams) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pInputParams));
    inputParams = pInputParams;
  }

  public Function<List<Object>, String> getFunctionToString() {
    return functionToString;
  }

  public void setFunctionToString(Function<List<Object>, String> pFunctionToString) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pFunctionToString));
    functionToString = pFunctionToString;
  }

  public void setArrayIndexType(String pArrayIndexType) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pArrayIndexType));
    arrayIndexType = pArrayIndexType;
  }

  public void setArrayValueType(String pArrayValueType) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pArrayValueType));
    arrayValueType = pArrayValueType;
  }

  public String getUFName() {
    return ufName;
  }

  public void setUFName(String pUFName) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pUFName));
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
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pUFInputType));
    ufInputType = pUFInputType;
  }

  public String getUFOutputType() {
    return ufOutputType;
  }

  public void setUFOutputType(String pUFOutputType) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pUFOutputType));
    ufOutputType = pUFOutputType;
  }
}
