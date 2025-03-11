// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static java.lang.Long.parseLong;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class BitvectorGenerator {
  private BitvectorGenerator() {}

  protected static void logMakeBitVector(Object result, int length, BigInteger i) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, i));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(Long.toString(length));
    inputParams.add(i.toString());
    Function<List<Object>, String> functionToString =
        inPlaceInputParamsString -> {
          // FIXME Fix the conversion to String
          String formatString = "%0" + length + "d";
          BigInteger binaryNumber =
              new BigInteger(
                  Long.toBinaryString(parseLong((String) inPlaceInputParamsString.get(1))));
          return "#b" + String.format(formatString, binaryNumber);
        };
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logMakeBitVector(BitvectorFormula result, int length, IntegerFormula pI) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pI));
    // TODO We need to convert the integer formula to bitvector. It doesn't have to be a constant.
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(Long.toString(length));
    inputParams.add(pI.toString());
    Function<List<Object>, String> functionToString =
        inPlaceInputParamsString -> {
          // FIXME Fix the conversion to String
          String formatString = "%0" + length + "d";
          int binaryNumber =
              Integer.parseInt(
                  Long.toBinaryString(parseLong((String) inPlaceInputParamsString.get(1))));
          return "#b" + String.format(formatString, binaryNumber);
        };
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logMakeBitVecVariable(
      BitvectorFormula result, BitvectorType pType, String pVar) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pType, pVar));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.BITVEC);
    newEntry.setBitVecLength(pType.getSize());
    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logMakeBitVecVariable(BitvectorFormula result, int pLength, String pVar) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pVar));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pVar);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.BITVEC);
    newEntry.setBitVecLength(pLength);
    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logBVEqual(
      Object result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(= " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVNegate(Object result, BitvectorFormula pNumber) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "(bvneg " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVAdd(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvadd " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVSub(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvsub " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVSDivide(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvsdiv " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVUDivide(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvudiv " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVSignedRemainder(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvsrem " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVUnsignedRemainder(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvurem " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVMultiply(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams ->
            "(bvmul " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logBVUGreaterThan(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvugt " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVSGreaterThan(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvsgt " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVUGreaterOrEqual(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvuge " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVSGreaterOrEqual(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvsge " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVULessThan(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvult " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVSLessThan(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvslt " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVULessOrEqual(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvule " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVSLessOrEqual(
      BooleanFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvsle " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVNot(Object result, BitvectorFormula pNumber) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams -> "(bvnot " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVAnd(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvand " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVOr(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvor " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVXor(
      BitvectorFormula result, BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber1, pNumber2));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber1);
    inputParams.add(pNumber2);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvxor " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVSShiftRight(
      BitvectorFormula result, BitvectorFormula pNumber, BitvectorFormula toShift) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber, toShift));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(toShift);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvashr " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVUShiftRight(
      BitvectorFormula result, BitvectorFormula pNumber, BitvectorFormula toShift) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber, toShift));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(toShift);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvlshr " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logBVShiftLeft(
      BitvectorFormula result, BitvectorFormula pNumber, BitvectorFormula toShift) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber, toShift));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(toShift);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(bvshl " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logConcat(
      BitvectorFormula result, BitvectorFormula pNumber, BitvectorFormula append) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber, append));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(append);
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "(concat " + inPlaceInputParams.get(0) + " " + inPlaceInputParams.get(1) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logExtract(
      BitvectorFormula result, BitvectorFormula pNumber, int pMsb, int pLsb) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(String.valueOf(pMsb));
    inputParams.add(String.valueOf(pLsb));
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "((_ extract "
                + inPlaceInputParams.get(1)
                + " "
                + inPlaceInputParams.get(2)
                + ") "
                + inPlaceInputParams.get(0)
                + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logUExtend(
      BitvectorFormula result, BitvectorFormula pNumber, int pExtensionBits) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(String.valueOf(pExtensionBits));
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "((_ zero_extend " + inPlaceInputParams.get(1) + ") " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }

  protected static void logSExtend(
      BitvectorFormula result, BitvectorFormula pNumber, int pExtensionBits) {
    Generator.throwExceptionWhenParameterIsNull(List.of(result, pNumber));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(pNumber);
    inputParams.add(String.valueOf(pExtensionBits));
    Function<List<Object>, String> saveResult =
        inPlaceInputParams ->
            "((_ sign_extend " + inPlaceInputParams.get(1) + ") " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, saveResult, Keyword.SKIP));
  }
}
