// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;
import org.sosy_lab.java_smt.solvers.SolverLess.SolverLessFloatingPointFormulaManager;

/**
 * This class logs all variable declarations, makeFloatingPoints and operations on FloatingPoint in
 * order to later generate SMTLIB2 code.
 */
public class FloatingPointGenerator {

  private FloatingPointGenerator() {}

  protected static void logMakeFloatingPoint(
      Object result, int exponent, int mantissa, String value) {
    List<Object> inputParams = new ArrayList<>();
    String output =
        SolverLessFloatingPointFormulaManager.makeNumberAndRoundStatic(
            value, FormulaType.getFloatingPointType(exponent, mantissa));
    inputParams.add(output);
    Function<List<Object>, String> functionToString = createString -> (String) createString.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logMakeFloatingPointVariable(
      FloatingPointFormula result, FloatingPointType type, String var) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(var);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.FLOATING_POINT);
    newEntry.floatingPointExponent = type.getExponentSize();
    newEntry.floatingPointMantissa = type.getMantissaSize();
    Generator.getExecutedAggregator().add(newEntry);
  }

  protected static void logFPMax(
      FloatingPointFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.max", num1, num2);
  }

  protected static void logFPMin(
      FloatingPointFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.min", num1, num2);
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
      FloatingPointFormula result,
      FloatingPointFormula num1,
      FloatingPointFormula num2,
      String roundingMode) {
    logBinaryOpWithMode(result, "fp.add", roundingMode, num1, num2);
  }

  protected static void logFPAdd(
      FloatingPointFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.add", num1, num2);
  }

  protected static void logFPMul(
      FloatingPointFormula result,
      FloatingPointFormula num1,
      FloatingPointFormula num2,
      String roundingMode) {
    logBinaryOpWithMode(result, "fp.mul", roundingMode, num1, num2);
  }

  protected static void logFPMul(
      FloatingPointFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.mul", num1, num2);
  }

  protected static void logFPDiv(
      FloatingPointFormula result,
      FloatingPointFormula num1,
      FloatingPointFormula num2,
      String roundingMode) {
    logBinaryOpWithMode(result, "fp.div", roundingMode, num1, num2);
  }

  protected static void logFPDiv(
      FloatingPointFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.div", num1, num2);
  }

  protected static void logFPSub(
      FloatingPointFormula result,
      FloatingPointFormula num1,
      FloatingPointFormula num2,
      String roundingMode) {
    logBinaryOpWithMode(result, "fp.sub", roundingMode, num1, num2);
  }

  protected static void logFPSub(
      FloatingPointFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.sub", num1, num2);
  }

  protected static void logFPSqrt(
      FloatingPointFormula result, FloatingPointFormula n, String roundingMode) {
    logUnaryOpWithMode(result, "fp.sqrt", roundingMode, n);
  }

  protected static void logFPSqrt(FloatingPointFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.sqrt", n);
  }

  protected static void logFPAbs(FloatingPointFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.abs", n);
  }

  protected static void logFPNegate(FloatingPointFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.neg", n);
  }

  protected static void logFPGreaterThan(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.gt", num1, num2);
  }

  protected static void logFPGreaterOrEquals(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.geq", num1, num2);
  }

  protected static void logFPLessThan(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.lt", num1, num2);
  }

  protected static void logFPLessOrEquals(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.leq", num1, num2);
  }

  protected static void logFPEqual(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.eq", num1, num2);
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

  protected static void logFPIsNormal(BooleanFormula result, FloatingPointFormula n) {
    logUnaryOp(result, "fp.isNormal", n);
  }

  protected static void logFPRound(
      FloatingPointFormula result, FloatingPointFormula n, String roundingMode) {
    logUnaryOpWithMode(result, "fp.round", roundingMode, n);
  }

  protected static void logFPAssignment(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "fp.assign", num1, num2);
  }

  protected static void logFPCastTo(
      Formula result,
      FloatingPointFormula number,
      String roundingMode,
      FormulaType<?> targetType,
      boolean signed) {
    String command;
    if (targetType.isIntegerType() || targetType.isRationalType() || targetType.isBitvectorType()) {
      if (targetType.isBitvectorType()) {
        if (!signed) {
          command = "_ fp.to_ubv";
        } else {
          command = "_ fp.to_sbv";
        }
      } else {
        command = "fp.to_real";
      }
    } else {
      throw new GeneratorException("Unsupported target type");
    }
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(roundingMode);
    inputParams.add(command);

    if (targetType.isBitvectorType()) {
      FormulaType.BitvectorType bitvectorFormulaFormulaType =
          (FormulaType.BitvectorType) targetType;
      inputParams.add(bitvectorFormulaFormulaType.getSize());
      Function<List<Object>, String> functionToString =
          inPlaceInputParams ->
              "(("
                  + inPlaceInputParams.get(2)
                  + " "
                  + inPlaceInputParams.get(3)
                  + " "
                  + inPlaceInputParams.get(1)
                  + ") "
                  + inPlaceInputParams.get(0)
                  + ")";
      Generator.getExecutedAggregator()
          .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
    } else if (targetType.isRationalType()) {
      Function<List<Object>, String> functionToString =
          inPlaceInputParams ->
              "(("
                  + inPlaceInputParams.get(2)
                  + " "
                  + inPlaceInputParams.get(1)
                  + ") "
                  + inPlaceInputParams.get(0)
                  + ")";
      Generator.getExecutedAggregator()
          .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
    }
  }

  protected static void logFPCastTo(
      Formula result, FloatingPointFormula number, FormulaType<?> targetType, boolean signed) {
    String command;
    if (targetType.isIntegerType() || targetType.isRationalType() || targetType.isBitvectorType()) {
      if (targetType.isBitvectorType()) {
        if (!signed) {
          command = "_ fp.to_ubv";
        } else {
          command = "_ fp.to_sbv";
        }
      } else {
        command = "fp.to_real";
      }
    } else {
      throw new GeneratorException("Unsupported target type");
    }
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(command);

    if (targetType.isBitvectorType()) {
      FormulaType.BitvectorType bitvectorFormulaFormulaType =
          (FormulaType.BitvectorType) targetType;
      inputParams.add(bitvectorFormulaFormulaType.getSize());
      Function<List<Object>, String> functionToString =
          inPlaceInputParams ->
              "(("
                  + inPlaceInputParams.get(1)
                  + " "
                  + inPlaceInputParams.get(2)
                  + ") "
                  + inPlaceInputParams.get(0)
                  + ")";
      Generator.getExecutedAggregator()
          .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
    } else if (targetType.isRationalType()) {
      Function<List<Object>, String> functionToString =
          inPlaceInputParams ->
              "((" + inPlaceInputParams.get(1) + ") " + inPlaceInputParams.get(0) + ")";
      Generator.getExecutedAggregator()
          .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
    }
  }

  protected static void logFPCastFrom(
      FloatingPointFormula result, Formula number, FloatingPointType type, String roundingMode) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(roundingMode);
    inputParams.add(String.valueOf(type.getExponentSize()));
    inputParams.add(String.valueOf(type.getMantissaSize()));
    Function<List<Object>, String> functionToString =
        getListStringFunctionForCast(number, inputParams);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logFPCastFrom(
      FloatingPointFormula result, Formula number, FloatingPointType type) {
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(String.valueOf(type.getExponentSize()));
    inputParams.add(String.valueOf(type.getMantissaSize()));
    Function<List<Object>, String> functionToString =
        getListStringFunctionForCast(number, inputParams);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  private static Function<List<Object>, String> getListStringFunctionForCast(
      Formula number, List<Object> inputParams) {
    if (inputParams.size() == 4) {
      Function<List<Object>, String> functionToString;
      if (number instanceof BitvectorFormula) {
        functionToString =
            inPlaceInputParams ->
                "((_ to_fp "
                    + inPlaceInputParams.get(2)
                    + " "
                    + inPlaceInputParams.get(3)
                    + ")"
                    + " "
                    + inPlaceInputParams.get(0)
                    + ")";
      } else {
        functionToString =
            inPlaceInputParams ->
                "((_ to_fp "
                    + inPlaceInputParams.get(2)
                    + " "
                    + inPlaceInputParams.get(3)
                    + ")"
                    + " "
                    + inPlaceInputParams.get(1)
                    + ") "
                    + inPlaceInputParams.get(0)
                    + ")";
      }
      return functionToString;
    } else {
      Function<List<Object>, String> functionToString;
      if (number instanceof BitvectorFormula) {
        functionToString =
            inPlaceInputParams ->
                "((_ to_fp "
                    + inPlaceInputParams.get(1)
                    + ")"
                    + " "
                    + inPlaceInputParams.get(0)
                    + ")";
      } else {
        functionToString =
            inPlaceInputParams ->
                "((_ to_fp "
                    + inPlaceInputParams.get(1)
                    + " "
                    + inPlaceInputParams.get(2)
                    + ") "
                    + inPlaceInputParams.get(0)
                    + ")";
      }
      return functionToString;
    }
  }

  protected static void logFromIeeeBitvector(
      FloatingPointFormula result, BitvectorFormula number, FloatingPointType type) {
    logUnaryOp(
        result, "((_ to_fp " + type.getExponentSize() + " " + type.getMantissaSize() + ")", number);
  }

  private static void logUnaryOp(Object result, String op, Object n) {
    List<Object> inputParams = ImmutableList.of(n);
    logOperation(result, inputParams, "(" + op + " %s)", Keyword.SKIP);
  }

  private static void logUnaryOpWithMode(Object result, String op, String mode, Object n) {
    List<Object> inputParams = ImmutableList.of(mode, n);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logBinaryOp(Object result, String op, Object num1, Object num2) {
    List<Object> inputParams = ImmutableList.of(num1, num2);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logBinaryOpWithMode(
      Object result, String op, String mode, Object num1, Object num2) {
    List<Object> inputParams = ImmutableList.of(mode, num1, num2);
    logOperation(result, inputParams, "(" + op + " %s %s %s)", Keyword.SKIP);
  }

  private static void logSimple(Object result, String expr) {
    List<Object> inputParams = new ArrayList<>();
    logOperation(result, inputParams, expr, Keyword.SKIP);
  }

  private static void logOperation(
      Object result, List<Object> params, String format, Keyword keyword) {
    Function<List<Object>, String> functionToString =
        inputs -> String.format(format, inputs.toArray());
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, params, functionToString, keyword));
  }
}
