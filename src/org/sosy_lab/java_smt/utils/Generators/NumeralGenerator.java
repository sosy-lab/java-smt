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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula;

public class NumeralGenerator {

  public static void logMakeNumber(Object result, String pVar) {
    if (result instanceof IntegerFormula && Integer.parseInt(pVar) < 0) {
      throw new UnsupportedOperationException("SMTLIB2 does not support negative integers");
    }
    List<Object> inputParams = new ArrayList<>();
    if (result instanceof NumeralFormula) {
      String checkedVar = String.valueOf(result);
      inputParams.add(checkedVar);
    } else {
      inputParams.add(pVar);
    }
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult,
        "Direct"));
  }

  public static void logMakeIntVariable(Object result, String pVar) {
    String varType;
    System.out.println(result.getClass());
    if (result instanceof IntegerFormula) {
      varType = "Int";
    } else {
      varType = "Real";
    }
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> saveResult = inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult,
        varType));
  }

  public static void logAdd(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(+ " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logEqual(Object result, NumeralFormula pNumber1, NumeralFormula pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logNegate(Object result, NumeralFormula pBits) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(- " + inPlaceInputParams.get(0) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logSum(Object result, List operands) {
    StringBuilder out = new StringBuilder();
    out.append("(+ ");
    List<Object> inputParams = new ArrayList<>();
    for (Object pOperand : operands) {
      inputParams.add(pOperand.toString());
    }
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> {
          inPlaceInputParams.forEach((c) -> {out.append(c); out.append(" ");}); return String.valueOf(
              out.deleteCharAt(out.length()-1).append(")"));};
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logSubtract(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(- " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logDivide(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(div " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logModulo(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(mod " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logModularCongruence(Object result, Object pNumber1, Object pNumber2,
                                          long pModulo) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    inputParams.add(Long.toString(pModulo));
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(= (mod " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(2) + ") (mod " + inPlaceInputParams.get(1) + " " + inPlaceInputParams.get(2) + "))";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logModularCongruence(Object result, Object pNumber1, Object pNumber2,
                                          BigInteger pModulo) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    inputParams.add(pModulo.toString());
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(= (mod " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(2) + ") (mod " + inPlaceInputParams.get(1) + " " + inPlaceInputParams.get(2) + "))";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logMultiply(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(* " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logDistinct(Object result, List operands) {
    StringBuilder out = new StringBuilder();
    out.append("(distinct ");
    List<Object> inputParams = new ArrayList<>();
    for (Object pOperand : operands) {
      inputParams.add(pOperand.toString());
    }
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> {
          inPlaceInputParams.forEach((c) -> {out.append(c); out.append(" ");}); return String.valueOf(
              out.deleteCharAt(out.length()-1).append(")"));};
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logGreaterThan(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(> " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logGreaterOrEquals(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(>= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logLessThan(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(< " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logLessOrEquals(Object result, Object pNumber1, Object pNumber2) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(<= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

  public static void logFloor(Object result, Object number) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(to_int " + inPlaceInputParams.get(0) + ")";
    Generator.executedAggregator.add(new RecursiveString<>(result, inputParams, saveResult, "Skip"));
  }

}
