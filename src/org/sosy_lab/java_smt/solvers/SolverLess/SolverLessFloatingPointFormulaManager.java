// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

@SuppressWarnings("StringSplitter")
public class SolverLessFloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<
        SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFloatingPointFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }

  @Override
  protected SMTLIB2Formula getDefaultRoundingMode() {
    return new SMTLIB2Formula(new DummyType(FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN));
  }

  @Override
  protected SMTLIB2Formula getRoundingModeImpl(
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(new DummyType(pFloatingPointRoundingMode));
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(
      double pN, FloatingPointType pType, SMTLIB2Formula pFloatingPointRoundingMode) {
    String binaryRepresentation = convertToSMTLibBinary(pN, pType);
    SMTLIB2Formula formula =
        new SMTLIB2Formula(
            new DummyType(
                pType.getExponentSize(),
                pType.getMantissaSize(),
                pFloatingPointRoundingMode.getFormulaType().getRoundingMode()));
    formula.setRepresentation(binaryRepresentation);
    return formula;
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, boolean signBit, FloatingPointType type) {
    int i = signBit ? 1 : 0;
    return new SMTLIB2Formula(
        new DummyType(type.getExponentSize(), type.getMantissaSize()),
        i + exponent.toString() + mantissa);
  }

  @Override
  protected SMTLIB2Formula makeNumberAndRound(
      String pN, FloatingPointType pType, SMTLIB2Formula pFloatingPointRoundingMode) {
    if (pN.matches("\\d+/\\d+")) {
      String[] parts = pN.split("/");
      BigDecimal numerator = new BigDecimal(parts[0]);
      BigDecimal denominator = new BigDecimal(parts[1]);
      double value = numerator.divide(denominator).doubleValue();
      return makeNumberImpl(value, pType, pFloatingPointRoundingMode);
    }
    try {
      double value = Double.parseDouble(pN);
      return makeNumberImpl(value, pType, pFloatingPointRoundingMode);
    } catch (NumberFormatException e) {
      throw new IllegalArgumentException("Unsupported number format: " + pN, e);
    }
  }

  public static <T> String makeNumberAndRoundStatic(T pN, FloatingPointType pType) {
    if (pN instanceof Double) {
      return convertToSMTLibBinary((Double) pN, pType);
    } else if (pN instanceof Integer) {
      return convertToSMTLibBinary(((Integer) pN).doubleValue(), pType);
    } else if (pN instanceof BigDecimal) {
      return convertToSMTLibBinary(((BigDecimal) pN).doubleValue(), pType);
    } else if (pN instanceof Rational) {
      return convertToSMTLibBinary(((Rational) pN).doubleValue(), pType);
    } else if (pN instanceof String) {
      String str = (String) pN;
      if (str.matches("\\d+/\\d+")) {
        return str;
      }
      try {
        return convertToSMTLibBinary(new BigDecimal(str).doubleValue(), pType);
      } catch (NumberFormatException e) {
        throw new IllegalArgumentException("Unsupported number format: " + pN, e);
      }
    } else {
      throw new IllegalArgumentException(
          "Unsupported number type: " + pN.getClass().getSimpleName());
    }
  }

  @Override
  protected SMTLIB2Formula makePlusInfinityImpl(FloatingPointType pType) {
    SMTLIB2Formula formula = new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setRepresentation(
        "(fp #b0 #b"
            + generateOnes(pType.getExponentSize())
            + " #b"
            + generateZeros(pType.getMantissaSize() - 1)
            + ")");
    return formula;
  }

  @Override
  protected SMTLIB2Formula makeMinusInfinityImpl(FloatingPointType pType) {
    SMTLIB2Formula formula = new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setRepresentation(
        "(fp #b1 #b"
            + generateOnes(pType.getExponentSize())
            + " #b"
            + generateZeros(pType.getMantissaSize() - 1)
            + ")");
    return formula;
  }

  @Override
  protected SMTLIB2Formula makeNaNImpl(FloatingPointType pType) {
    SMTLIB2Formula formula = new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setRepresentation(
        "(fp #b0 #b"
            + generateOnes(pType.getExponentSize())
            + " #b1"
            + generateZeros(pType.getMantissaSize() - 2)
            + ")");
    return formula;
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

  public static String generateOnes(int count) {
    return "1".repeat(Math.max(0, count));
  }

  public static String generateZeros(int count) {
    return "0".repeat(Math.max(0, count));
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(String pVar, FloatingPointType pType) {
    SMTLIB2Formula formula = new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setName(pVar);
    return formula;
  }

  // Rest of the methods remain unchanged...
  @Override
  protected SMTLIB2Formula castToImpl(
      SMTLIB2Formula pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      SMTLIB2Formula pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      return new SMTLIB2Formula(targetType.getExponentSize(), targetType.getMantissaSize());
    }
    if (pTargetType.isIntegerType()) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
    }
    if (pTargetType.isBitvectorType()) {
      BitvectorType targetType = (BitvectorType) pTargetType;
      return new SMTLIB2Formula(targetType.getSize());
    }
    if (pTargetType.isRationalType()) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.RATIONAL));
    }
    return null;
  }

  @Override
  protected SMTLIB2Formula castFromImpl(
      SMTLIB2Formula pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      SMTLIB2Formula pRoundingMode) {
    return new SMTLIB2Formula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula fromIeeeBitvectorImpl(
      SMTLIB2Formula pNumber, FloatingPointType pTargetType) {
    return new SMTLIB2Formula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected SMTLIB2Formula toIeeeBitvectorImpl(SMTLIB2Formula pNumber) {
    return new SMTLIB2Formula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected SMTLIB2Formula negate(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula abs(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula max(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula min(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula sqrt(SMTLIB2Formula pNumber, SMTLIB2Formula pRoundingMode) {
    return new SMTLIB2Formula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected SMTLIB2Formula add(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula subtract(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula divide(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula multiply(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, SMTLIB2Formula pFloatingPointRoundingMode) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula remainder(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return null;
  }

  @Override
  protected SMTLIB2Formula assignment(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected SMTLIB2Formula equalWithFPSemantics(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isNaN(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isInfinity(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isZero(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isSubnormal(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isNormal(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula isNegative(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula round(SMTLIB2Formula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return new SMTLIB2Formula(pFormula.getExponent(), pFormula.getMantissa());
  }
}
