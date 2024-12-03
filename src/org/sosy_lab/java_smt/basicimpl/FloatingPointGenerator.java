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

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

public class FloatingPointGenerator {

  private FloatingPointGenerator() {}

  protected static void logMakeFloatingPoint(Object result, int exponent, int mantissa) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(exponent);
    inputParams.add(mantissa);
    Function<List<Object>, String> functionToString = createString ->
        "(_ FloatingPoint " + createString.get(0) + " " + createString.get(1) + ")";
    Generator.getExecutedAggregator().add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP)
    );
  }

  protected static void logMakeFloatingPointVariable(
      FloatingPointFormula result, FloatingPointType type, String var) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(var);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    FunctionEnvironment newEntry = new FunctionEnvironment(result, inputParams, functionToString,
        Keyword.FLOATING_POINT);
    newEntry.exponent = type.getExponentSize();
    newEntry.mantissa = type.getMantissaSize();
    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logFPMax(FloatingPointFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.max", n1, n2);
  }

  protected static void logFPMin(FloatingPointFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.min", n1, n2);
  }


  protected static void logMakeNaN(FloatingPointFormula result, FloatingPointType type) {
    logSimple(result, "(_ NaN " + type.getExponentSize() + " " + type.getMantissaSize() + ")");
  }

  protected static void logMakePlusInfinity(FloatingPointFormula result, FloatingPointType type) {
    logSimple(result, "(_ +oo " + type.getExponentSize() + " " + type.getMantissaSize() + ")");
  }

  protected static void logMakeMinusInfinity(FloatingPointFormula result, FloatingPointType type) {
    logSimple(result, "(_ -oo " + type.getExponentSize() + " " + type.getMantissaSize() + ")");
  }


  protected static void logFPAdd(
      FloatingPointFormula result, FloatingPointFormula n1, FloatingPointFormula n2, String roundingMode) {
    logBinaryOpWithMode(result, "fp.add", roundingMode, n1, n2);
  }

  protected static void logFPMul(
      FloatingPointFormula result, FloatingPointFormula n1, FloatingPointFormula n2, String roundingMode) {
    logBinaryOpWithMode(result, "fp.mul", roundingMode, n1, n2);
  }

  protected static void logFPDiv(
      FloatingPointFormula result, FloatingPointFormula n1, FloatingPointFormula n2, String roundingMode) {
    logBinaryOpWithMode(result, "fp.div", roundingMode, n1, n2);
  }

  protected static void logFPSub(
      FloatingPointFormula result, FloatingPointFormula n1, FloatingPointFormula n2, String roundingMode) {
    logBinaryOpWithMode(result, "fp.sub", roundingMode, n1, n2);
  }

  protected static void logFPSqrt(FloatingPointFormula result, FloatingPointFormula n, String roundingMode) {
    logUnaryOpWithMode(result, "fp.sqrt", roundingMode, n);
  }

  protected static void logFPAbs(FloatingPointFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.abs", n);
  }

  protected static void logFPNegate(FloatingPointFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.neg", n);
  }


  protected static void logFPGreaterThan(BooleanFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.gt", n1, n2);
  }

  protected static void logFPGreaterOrEquals(BooleanFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.geq", n1, n2);
  }

  protected static void logFPLessThan(BooleanFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.lt", n1, n2);
  }

  protected static void logFPLessOrEquals(BooleanFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.leq", n1, n2);
  }

  protected static void logFPEqual(BooleanFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.eq", n1, n2);
  }


  protected static void logFPIsNaN(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isNaN", n);
  }

  protected static void logFPIsZero(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isZero", n);
  }

  protected static void logFPIsInfinite(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isInfinite", n);
  }

  protected static void logFPIsSubnormal(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isSubnormal", n);
  }

  protected static void logFPIsNegative(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isNegative", n);
  }
  protected static void logFPIsPositive(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isPositive", n);
  }
  protected static void logFPIsNormal(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isNormal", n);
  }

  protected static void logFPCast(FloatingPointFormula result, Formula source, String roundingMode, FloatingPointType type) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(source);
    inputParams.add(roundingMode);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> "((_ to_fp " + inPlaceInputParams.get(1) + ") " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator().add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP)
    );
  }

  // FloatingPointGenerator - Ergänzung der fehlenden Funktionen
  protected static void logFPRound(
      FloatingPointFormula result, FloatingPointFormula n, String roundingMode) {
    logUnaryOpWithMode(result, "fp.round", roundingMode, n);
  }

  protected static void logFPAssignment(BooleanFormula result, FloatingPointFormula n1, FloatingPointFormula n2) {
    logBinaryOp(result, "fp.assign", n1, n2);
  }

  protected static void logFPCastTo(
      Formula result, FloatingPointFormula number, String targetType, String roundingMode) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(roundingMode);
    Function<List<Object>, String> functionToString = inPlaceInputParams ->
        "((_ to_" + targetType + " " + inPlaceInputParams.get(1) + ") " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator().add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP)
    );
  }

  protected static void logFPCastFrom(
      FloatingPointFormula result, Formula number, String sourceType, String roundingMode) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(roundingMode);
    Function<List<Object>, String> functionToString = inPlaceInputParams ->
        "((_ from_" + sourceType + " " + inPlaceInputParams.get(1) + ") " + inPlaceInputParams.get(0) + ")";
    Generator.getExecutedAggregator().add(
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP)
    );
  }

  protected static void logFromIeeeBitvector(
      FloatingPointFormula result, BitvectorFormula number, FloatingPointType type) {
    logSimple(result, "((_ to_fp " + type.getExponentSize() + " " + type.getMantissaSize() + ") " + number + ")");
  }

  protected static void logToIeeeBitvector(BitvectorFormula result, FloatingPointFormula number) {
    logUnaryOp(result, "fp.to_ieee", number);
  }


  private static void logUnaryOp(Object result, String op, Object n) {
    List<Object> inputParams = List.of(n);
    logOperation(result, inputParams, "(" + op + " %s)", Keyword.SKIP);
  }

  private static void logUnaryOpWithMode(Object result, String op, String mode, Object n) {
    List<Object> inputParams = List.of(mode, n);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logBinaryOp(Object result, String op, Object n1, Object n2) {
    List<Object> inputParams = List.of(n1, n2);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logBinaryOpWithMode(Object result, String op, String mode, Object n1, Object n2) {
    List<Object> inputParams = List.of(mode, n1, n2);
    logOperation(result, inputParams, "(" + op + " %s %s %s)", Keyword.SKIP);
  }

  private static void logSimple(Object result, String expr) {
    List<Object> inputParams = new ArrayList<>();
    logOperation(result, inputParams, expr, Keyword.SKIP);
  }

  private static void logOperation(Object result, List<Object> params, String format, Keyword keyword) {
    Function<List<Object>, String> functionToString = inputs -> String.format(format, inputs.toArray());
    Generator.getExecutedAggregator().add(
        new FunctionEnvironment(result, params, functionToString, keyword)
    );
  }
}
