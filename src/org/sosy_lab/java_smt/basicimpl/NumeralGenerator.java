// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class NumeralGenerator {
  private NumeralGenerator() {}

  /**
   * @param result solver returned object for the makeNumber() call.
   * @param number the value of the number as String.
   */
  protected static void logMakeNumber(Object result, String number) {
    List<Object> inputParams = new ArrayList<>();
    Function<List<Object>, String> functionToString;
    if (result instanceof IntegerFormula && new BigInteger(number).signum() == -1) {
      BigInteger numberValueBigInt = new BigInteger(number);
      String absVar = String.valueOf(numberValueBigInt.abs());
      inputParams.add(absVar);
      functionToString = inPlaceInputParams -> "(- " + inPlaceInputParams.get(0) + ")";

    } else {
      inputParams.add(number);
      functionToString = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    }

    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logMakeIntVariable(Object result, String pVar) {
    Keyword varType;
    if (result instanceof IntegerFormula) {
      varType = Keyword.INT;
    } else {
      varType = Keyword.REAL;
    }
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, varType));
  }

  protected static void logAdd(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(+ " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logEqual(Object result, NumeralFormula pNumber1, NumeralFormula pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logNegate(Object result, NumeralFormula pBits) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "(- " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
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
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logSubtract(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(- " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logDivide(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(div " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logModulo(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(mod " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logMultiply(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(* " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
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
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logGreaterThan(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(> " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logGreaterOrEquals(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(>= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logLessThan(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(< " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logLessOrEquals(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(<= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logFloor(Object result, Object number) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "(to_int " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }
}
