// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.Generator.Keyword;

/**
 * This class logs all variable declarations, makeFloatingPoints and operations on FloatingPoint in
 * order to later generate SMTLIB2 code.
 */
public class FloatingPointGenerator {

  private FloatingPointGenerator() {}

  protected static void logMakeFloatingPoint(
      Object result, int exponent, int mantissa, Object value) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, value));
    List<Object> inputParams = new ArrayList<>();
    String output =
        makeNumberAndRoundStatic(value, FormulaType.getFloatingPointType(exponent, mantissa));
    inputParams.add(output);
    Function<List<Object>, String> functionToString = createString -> (String) createString.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logMakeFloatingPointFromBigInteger(
      Object result,
      BigInteger exponent,
      BigInteger mantissa,
      boolean sign,
      FloatingPointType type) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(exponent, mantissa, type));
    List<Object> inputParams = new ArrayList<>();
    // SIGN BIT
    String output = "(fp ";
    if (sign) {
      output += "#b1 ";
    } else {
      output += "#b0 ";
    }
    // EXPONENT
    if (exponent.toString().length() == type.getExponentSize()) {
      output += "#b";
    } else {
      output += "#x";
    }
    output += exponent + " ";
    // MANTISSA
    if (mantissa.toString().length() == type.getMantissaSize()) {
      output += "#b";
    } else {
      output += "#x";
    }
    output += mantissa + ")";
    inputParams.add(output);
    Function<List<Object>, String> functionToString = createString -> (String) createString.get(0);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  public static String makeNumberAndRoundStatic(Object pN, FloatingPointType pType) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(pN, pType));
    if (pN instanceof Double) {
      return convertToSMTLibBinary((Double) pN, pType);
    } else if (pN instanceof Integer) {
      return convertToSMTLibBinary((Integer) pN, pType);
    } else if (pN instanceof BigDecimal) {
      return convertToSMTLibBinary((BigDecimal) pN, pType);
    } else if (pN instanceof Rational) {
      return convertToSMTLibBinary((Rational) pN, pType);
    } else if (pN instanceof String) {
      String str = (String) pN;

      // Check if the string represents a rational number (fraction)
      if (str.matches("-?\\d+/\\d+")) {
        // Parse as Rational number (e.g., "3/4")
        return convertToSMTLibBinary(Rational.of(str), pType);
      }

      // Try to convert to BigDecimal first to avoid precision loss
      try {
        BigDecimal decimalValue = new BigDecimal(str);
        return convertToSMTLibBinary(decimalValue, pType);
      } catch (NumberFormatException e) {
        throw new IllegalArgumentException("Unsupported number format: " + pN, e);
      }
    } else {
      throw new IllegalArgumentException(
          "Unsupported number type: " + pN.getClass().getSimpleName());
    }
  }

  public static String convertToSMTLibBinaryForInteger(int value, FloatingPointType type) {
    int exponentSize = type.getExponentSize();
    int mantissaSize = type.getMantissaSize();

    // Handle special case for zero
    if (value == 0) {
      return "(fp #b0 #b" + generateZeros(exponentSize) + " #b" + generateZeros(mantissaSize) + ")";
    }

    // Determine the sign bit
    int signBit = (value < 0) ? 1 : 0;
    int absValue = Math.abs(value);

    // Calculate exponent and mantissa
    int exponent = 0;
    while (absValue >= (1 << exponentSize)) {
      absValue >>= 1; // equivalent to dividing by 2
      exponent++;
    }

    // Bias calculation
    int bias = (1 << (exponentSize - 1)) - 1;
    int biasedExponent = exponent + bias;

    // Handle denormal numbers (when exponent is too small)
    if (biasedExponent <= 0) {
      return "(fp #b"
          + signBit
          + " #b"
          + generateZeros(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    // Handle overflow (infinity)
    if (biasedExponent >= (1 << exponentSize) - 1) {
      return "(fp #b"
          + signBit
          + " #b"
          + generateOnes(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    // Convert the integer to its binary representation for mantissa
    StringBuilder mantissaBits = new StringBuilder();
    while (absValue > 0 && mantissaBits.length() < mantissaSize) {
      mantissaBits.insert(0, (absValue & 1)); // Add the least significant bit to mantissa
      absValue >>= 1; // shift right to process next bit
    }

    // If mantissa is smaller than mantissaSize, pad with zeros
    while (mantissaBits.length() < mantissaSize) {
      mantissaBits.insert(0, "0");
    }

    // Return the SMT-LIB formatted string
    return "(fp #b"
        + signBit
        + " #b"
        + String.format("%" + exponentSize + "s", Integer.toBinaryString(biasedExponent))
            .replace(' ', '0')
        + " #b"
        + mantissaBits
        + ")";
  }

  public static String convertToSMTLibBinary(double value, FloatingPointType type) {
    int exponentSize = type.getExponentSize();
    int mantissaSize = type.getMantissaSize();

    // Handle special cases
    if (Double.isNaN(value)) {
      return "(fp #b0 #b"
          + generateOnes(exponentSize)
          + " #b1"
          + generateZeros(mantissaSize - 1)
          + ")";
    } else if (Double.isInfinite(value)) {
      String sign = (value < 0) ? "1" : "0";
      return "(fp #b"
          + sign
          + " #b"
          + generateOnes(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    } else if (value == 0.0) {
      String sign = (1 / value < 0) ? "1" : "0"; // handle -0.0
      return "(fp #b"
          + sign
          + " #b"
          + generateZeros(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    int signBit = (value < 0) ? 1 : 0;
    double absValue = Math.abs(value);

    // Calculate exponent and mantissa
    int exponent = 0;
    while (absValue >= 2.0) {
      absValue /= 2.0;
      exponent++;
    }
    while (absValue < 1.0) {
      absValue *= 2.0;
      exponent--;
    }

    // Bias calculation
    int bias = (1 << (exponentSize - 1)) - 1;
    int biasedExponent = exponent + bias;

    // Handle denormal numbers
    if (biasedExponent <= 0) {
      return "(fp #b"
          + signBit
          + " #b"
          + generateZeros(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    // Handle overflow (infinity)
    if (biasedExponent >= (1 << exponentSize) - 1) {
      return "(fp #b"
          + signBit
          + " #b"
          + generateOnes(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    // Calculate mantissa bits (without the implicit leading 1)
    StringBuilder mantissaBits = new StringBuilder();
    double remaining = absValue - 1.0;

    for (int i = 0; i < mantissaSize; i++) {
      remaining *= 2;
      if (remaining >= 1.0) {
        mantissaBits.append("1");
        remaining -= 1.0;
      } else {
        mantissaBits.append("0");
      }
    }

    // Simple rounding
    if (remaining >= 0.5) {
      // Need to round up
      boolean carry = true;
      for (int i = mantissaBits.length() - 1; i >= 0 && carry; i--) {
        if (mantissaBits.charAt(i) == '0') {
          mantissaBits.setCharAt(i, '1');
          carry = false;
        } else {
          mantissaBits.setCharAt(i, '0');
        }
      }
      if (carry) {
        biasedExponent++;
        mantissaBits = new StringBuilder(generateZeros(mantissaSize));
      }
    }

    String exponentBits =
        String.format("%" + exponentSize + "s", Integer.toBinaryString(biasedExponent))
            .replace(' ', '0');

    return "(fp #b" + signBit + " #b" + exponentBits + " #b" + mantissaBits + ")";
  }

  public static String convertToSMTLibBinary(BigDecimal value, FloatingPointType type) {
    int exponentSize = type.getExponentSize();
    int mantissaSize = type.getMantissaSize();

    // Handle zero
    if (value.compareTo(BigDecimal.ZERO) == 0) {
      String sign = (value.signum() < 0) ? "1" : "0";
      return "(fp #b"
          + sign
          + " #b"
          + generateZeros(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    int signBit = value.signum() < 0 ? 1 : 0;
    BigDecimal absValue = value.abs();

    // Calculate exponent and mantissa
    int exponent = 0;
    while (absValue.compareTo(BigDecimal.valueOf(2)) >= 0) {
      absValue = absValue.divide(BigDecimal.valueOf(2), MathContext.DECIMAL128);
      exponent++;
    }
    while (absValue.compareTo(BigDecimal.ONE) < 0) {
      absValue = absValue.multiply(BigDecimal.valueOf(2), MathContext.DECIMAL128);
      exponent--;
    }

    // Bias calculation
    int bias = (1 << (exponentSize - 1)) - 1;
    int biasedExponent = exponent + bias;

    // Handle denormal numbers
    if (biasedExponent <= 0) {
      return "(fp #b"
          + signBit
          + " #b"
          + generateZeros(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    // Handle overflow (infinity)
    if (biasedExponent >= (1 << exponentSize) - 1) {
      return "(fp #b"
          + signBit
          + " #b"
          + generateOnes(exponentSize)
          + " #b"
          + generateZeros(mantissaSize)
          + ")";
    }

    // Calculate mantissa bits
    StringBuilder mantissaBits = new StringBuilder();
    BigDecimal remainder = absValue.subtract(BigDecimal.ONE);

    for (int i = 0; i < mantissaSize; i++) {
      remainder = remainder.multiply(BigDecimal.valueOf(2));
      if (remainder.compareTo(BigDecimal.ONE) >= 0) {
        mantissaBits.append("1");
        remainder = remainder.subtract(BigDecimal.ONE);
      } else {
        mantissaBits.append("0");
      }
    }

    // Rounding
    if (remainder.compareTo(BigDecimal.valueOf(0.5)) >= 0) {
      // Need to round up
      boolean carry = true;
      for (int i = mantissaBits.length() - 1; i >= 0 && carry; i--) {
        if (mantissaBits.charAt(i) == '0') {
          mantissaBits.setCharAt(i, '1');
          carry = false;
        } else {
          mantissaBits.setCharAt(i, '0');
        }
      }
      if (carry) {
        biasedExponent++;
        mantissaBits = new StringBuilder(generateZeros(mantissaSize));
      }
    }

    String exponentBits = Integer.toBinaryString(biasedExponent);
    exponentBits = padWithZeros(exponentBits, exponentSize);

    return "(fp #b" + signBit + " #b" + exponentBits + " #b" + mantissaBits + ")";
  }

  public static String convertToSMTLibBinary(Rational value, FloatingPointType type) {
    // Input validation
    Objects.requireNonNull(value, "Rational value cannot be null");
    Objects.requireNonNull(type, "FloatingPointType cannot be null");

    final int exponentSize = type.getExponentSize();
    final int mantissaSize = type.getMantissaSize();
    final int bias = (1 << (exponentSize - 1)) - 1;
    final Rational two = Rational.ofLong(2);
    final Rational one = Rational.ofLong(1);
    final Rational half = Rational.ofLongs(1, 2);

    // Handle zero
    if (value.equals(Rational.ZERO)) {
      String sign = value.signum() < 0 ? "1" : "0";
      return String.format(
          "(fp #b%s #b%s #b%s)", sign, generateZeros(exponentSize), generateZeros(mantissaSize));
    }

    final int signBit = value.signum() < 0 ? 1 : 0;
    Rational absValue = value.abs();

    // Calculate exponent
    int exponent = 0;
    if (absValue.compareTo(one) >= 0) {
      while (absValue.compareTo(two) >= 0) {
        absValue = absValue.divides(two);
        exponent++;
      }
    } else {
      while (absValue.compareTo(one) < 0) {
        absValue = absValue.times(two);
        exponent--;
      }
    }

    // Handle special cases after exponent calculation
    int biasedExponent = exponent + bias;

    // Handle denormal numbers
    if (biasedExponent <= 0) {
      return String.format(
          "(fp #b%s #b%s #b%s)", signBit, generateZeros(exponentSize), generateZeros(mantissaSize));
    }

    // Handle overflow (infinity)
    if (biasedExponent >= (1 << exponentSize) - 1) {
      return String.format(
          "(fp #b%s #b%s #b%s)", signBit, generateOnes(exponentSize), generateZeros(mantissaSize));
    }

    // Calculate mantissa bits
    StringBuilder mantissaBits = new StringBuilder(mantissaSize);
    Rational remainder = absValue.minus(one);

    for (int i = 0; i < mantissaSize; i++) {
      remainder = remainder.times(two);
      if (remainder.compareTo(one) >= 0) {
        mantissaBits.append('1');
        remainder = remainder.minus(one);
      } else {
        mantissaBits.append('0');
      }
    }

    // Rounding - round to nearest, ties to even
    if (remainder.compareTo(half) > 0
        || (remainder.equals(half) && mantissaBits.charAt(mantissaSize - 1) == '1')) {
      // Need to round up
      boolean carry = true;
      for (int i = mantissaSize - 1; i >= 0 && carry; i--) {
        if (mantissaBits.charAt(i) == '0') {
          mantissaBits.setCharAt(i, '1');
          carry = false;
        } else {
          mantissaBits.setCharAt(i, '0');
        }
      }
      if (carry) {
        biasedExponent++;
        if (biasedExponent >= (1 << exponentSize) - 1) {
          return String.format(
              "(fp #b%s #b%s #b%s)",
              signBit, generateOnes(exponentSize), generateZeros(mantissaSize));
        }
        mantissaBits = new StringBuilder(generateZeros(mantissaSize));
      }
    }

    String exponentBits = padWithZeros(Integer.toBinaryString(biasedExponent), exponentSize);
    return String.format("(fp #b%s #b%s #b%s)", signBit, exponentBits, mantissaBits);
  }

  private static String padWithZeros(String s, int length) {
    while (s.length() < length) {
      s = "0" + s;
    }
    return s;
  }

  public static String generateOnes(int count) {
    return "1".repeat(Math.max(0, count));
  }

  public static String generateZeros(int count) {
    return "0".repeat(Math.max(0, count));
  }

  protected static void logMakeFloatingPointVariable(
      FloatingPointFormula result, FloatingPointType type, String var) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, type, var));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(var);
    Function<List<Object>, String> functionToString =
        inPlaceInputParams -> (String) inPlaceInputParams.get(0);
    FunctionEnvironment newEntry =
        new FunctionEnvironment(result, inputParams, functionToString, Keyword.FLOATING_POINT);
    newEntry.floatingPointExponent = type.getExponentSize();
    newEntry.floatingPointMantissa = type.getMantissaSize() + 1;
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
    logSimple(
        result, "(_ NaN " + type.getExponentSize() + " " + (type.getMantissaSize() + 1) + ")");
  }

  protected static void logMakePlusInfinity(FloatingPointFormula result, FloatingPointType type) {
    logSimple(
        result, "(_ +oo " + type.getExponentSize() + " " + (type.getMantissaSize() + 1) + ")");
  }

  protected static void logMakeMinusInfinity(FloatingPointFormula result, FloatingPointType type) {
    logSimple(
        result, "(_ -oo " + type.getExponentSize() + " " + (type.getMantissaSize() + 1) + ")");
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
    logUnaryOpWithMode(result, "fp.roundToIntegral", roundingMode, n);
  }

  protected static void logFPAssignment(
      BooleanFormula result, FloatingPointFormula num1, FloatingPointFormula num2) {
    logBinaryOp(result, "=", num1, num2);
  }

  protected static void logFPCastTo(
      Formula result,
      FloatingPointFormula number,
      String roundingMode,
      FormulaType<?> targetType,
      boolean signed) {
    Generator.throwExceptionWhenParameterIsNull(
        ImmutableList.of(result, number, targetType, roundingMode));
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
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, number, targetType));
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
    Generator.throwExceptionWhenParameterIsNull(
        ImmutableList.of(result, number, type, roundingMode));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(roundingMode);
    inputParams.add(String.valueOf(type.getExponentSize()));
    inputParams.add(String.valueOf(type.getMantissaSize() + 1));
    Function<List<Object>, String> functionToString =
        getListStringFunctionForCast(number, inputParams);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  protected static void logFPCastFrom(
      FloatingPointFormula result, Formula number, FloatingPointType type) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, number, type));
    List<Object> inputParams = new ArrayList<>();
    inputParams.add(number);
    inputParams.add(String.valueOf(type.getExponentSize()));
    inputParams.add(String.valueOf(type.getMantissaSize() + 1));
    Function<List<Object>, String> functionToString =
        getListStringFunctionForCast(number, inputParams);
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, inputParams, functionToString, Keyword.SKIP));
  }

  private static Function<List<Object>, String> getListStringFunctionForCast(
      Formula number, List<Object> inputParams) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(number, inputParams));
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
                    + " "
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
        result,
        "(_ to_fp " + type.getExponentSize() + " " + (type.getMantissaSize() + 1) + ")",
        number);
  }

  private static void logUnaryOp(Object result, String op, Object n) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, op, n));
    List<Object> inputParams = ImmutableList.of(n);
    logOperation(result, inputParams, "(" + op + " %s)", Keyword.SKIP);
  }

  private static void logUnaryOpWithMode(Object result, String op, String mode, Object n) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, op, mode, n));
    List<Object> inputParams = ImmutableList.of(mode, n);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logBinaryOp(Object result, String op, Object num1, Object num2) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, op, num1, num2));
    List<Object> inputParams = ImmutableList.of(num1, num2);
    logOperation(result, inputParams, "(" + op + " %s %s)", Keyword.SKIP);
  }

  private static void logBinaryOpWithMode(
      Object result, String op, String mode, Object num1, Object num2) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, op, mode, num1, num2));
    List<Object> inputParams = ImmutableList.of(mode, num1, num2);
    logOperation(result, inputParams, "(" + op + " %s %s %s)", Keyword.SKIP);
  }

  private static void logSimple(Object result, String expr) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, expr));
    List<Object> inputParams = new ArrayList<>();
    logOperation(result, inputParams, expr, Keyword.SKIP);
  }

  private static void logOperation(
      Object result, List<Object> params, String format, Keyword keyword) {
    Generator.throwExceptionWhenParameterIsNull(ImmutableList.of(result, params, format, keyword));
    Function<List<Object>, String> functionToString =
        inputs -> String.format(format, inputs.toArray());
    Generator.getExecutedAggregator()
        .add(new FunctionEnvironment(result, params, functionToString, keyword));
  }
}
