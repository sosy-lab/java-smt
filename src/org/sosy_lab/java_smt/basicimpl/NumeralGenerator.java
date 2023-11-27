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

package org.sosy_lab.java_smt.basicimpl;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class NumeralGenerator {

  protected static void logMakeNumber(Object result, String pVar) {
    List<Object> inputParams = new ArrayList<>();
    if (result instanceof IntegerFormula && new BigInteger(pVar).signum() == 0) {
      BigInteger input = new BigInteger(pVar);
      String absVar = String.valueOf( input.abs());
      inputParams.add(absVar);
      Function<List<Object>, String> functionToString =
          inPlaceInputParams -> "(- " + inPlaceInputParams.get(0) + ")";
      Generator.executedAggregator.add(
          new FunctionEnvironment(result, inputParams, functionToString, "Direct"));
    } else if (result instanceof NumeralFormula) {
      String checkedVar = String.valueOf(result);
      inputParams.add(checkedVar);
    } else {
      inputParams.add(pVar);
    }
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Direct"));
  }

  protected static void logMakeIntVariable(Object result, String pVar) {
    String varType;
    if (result instanceof IntegerFormula) {
      varType = "Int";
    } else {
      varType = "Real";
    }
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, varType));
  }

  protected static void logAdd(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(+ " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logEqual(Object result, NumeralFormula pNumber1, NumeralFormula pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logNegate(Object result, NumeralFormula pBits) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "(- " + inPlaceInputParams.get(0) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logSum(Object result, List<?> operands) {

    List<Object> inputParams = new ArrayList<>();
    for (Object pOperand : operands) {
      inputParams.add(pOperand.toString());
    }
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.append("(+ ");
          inPlaceInputParams.forEach(
              (c) -> {
                out.append(c);
                out.append(" ");
              });
          return String.valueOf(out.deleteCharAt(out.length() - 1).append(")"));
        };
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logSubtract(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(- " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logDivide(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(div " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logModulo(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(mod " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logMultiply(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(* " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logDistinct(Object result, List<?> operands) {
    List<Object> inputParams = new ArrayList<>();
    for (Object pOperand : operands) {
      inputParams.add(pOperand.toString());
    }
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.append("(distinct ");
          inPlaceInputParams.forEach(
              (c) -> {
                out.append(c);
                out.append(" ");
              });
          return String.valueOf(out.deleteCharAt(out.length() - 1).append(")"));
        };
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logGreaterThan(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(> " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logGreaterOrEquals(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(>= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logLessThan(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(< " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logLessOrEquals(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(<= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }

  protected static void logFloor(Object result, Object number) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "(to_int " + inPlaceInputParams.get(0) + ")";
    Generator.executedAggregator.add(
        new FunctionEnvironment(result, inputParams, functionToString, "Skip"));
  }
}
