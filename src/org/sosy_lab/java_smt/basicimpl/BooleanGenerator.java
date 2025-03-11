// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class BooleanGenerator {
  private BooleanGenerator() {}

  protected static void logMakeVariable(Object result, String pVar) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pVar));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.BOOL));
  }

  protected static void logMakeTrue(Object result, String pVar) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pVar));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.DIRECT));
  }

  protected static void logMakeFalse(Object result, String pVar) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pVar));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.DIRECT));
  }

  protected static void logNot(Object result, BooleanFormula pBits) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "(not " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logOr(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1, pBits2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(or " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logOr(Object result, Collection<BooleanFormula> pBits1) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1));
    List<Object> inputParams = new ArrayList<>(pBits1);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.append("(or ");
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

  protected static void logAnd(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1, pBits2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(and " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logAnd(Object result, Collection<BooleanFormula> pBits1) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1));
    List<Object> inputParams = new ArrayList<>(pBits1);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> {
          StringBuilder out = new StringBuilder();
          out.delete(0, out.length());
          out.append("(and ");
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

  protected static void logXor(Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1, pBits2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(xor " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logEquivalence(
      Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1, pBits2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logImplication(
      Object result, BooleanFormula pBits1, BooleanFormula pBits2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1, pBits2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(pBits2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(=> " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logIfThenElse(Object result, BooleanFormula pBits1, Object f1, Object f2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pBits1, f1, f2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pBits1);
    inputParams.add(f1);
    inputParams.add(f2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(ite "
                + inPlaceInputParams.get(0)
                + " "
                + inPlaceInputParams.get(1)
                + " "
                + inPlaceInputParams.get(2)
                + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }
}
