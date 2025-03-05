// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigDecimal;
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
    int signBit;
    int exponentBits;
    int mantissaBits;
    if (exponentSize == 8 && mantissaSize == 23) {
      int bits = Float.floatToRawIntBits((float) value);
      signBit = (bits >>> 31) & 1; // fill it with zros from the left until only the 1 or 0 is left
      exponentBits = (bits >>> mantissaSize) & ((1 << exponentSize) - 1);
      mantissaBits = bits & ((1 << mantissaSize) - 1);
    } else if (exponentSize == 11 && mantissaSize == 52) {
      long bits = Double.doubleToRawLongBits(value);
      signBit = (int) ((bits >>> 63) & 1);
      exponentBits = (int) ((bits >>> mantissaSize) & ((1L << exponentSize) - 1));
      mantissaBits = (int) (bits & ((1L << mantissaSize) - 1));
    } else {
      throw new IllegalArgumentException(
          "Unsupported FloatingPointType: " + exponentSize + ", " + mantissaSize);
    }
    String signStr = Integer.toBinaryString(signBit);
    String exponentStr =
        String.format("%" + exponentSize + "s", Integer.toBinaryString(exponentBits))
            .replace(' ', '0');
    String mantissaStr =
        String.format("%" + mantissaSize + "s", Integer.toBinaryString(mantissaBits))
            .replace(' ', '0');

    return "(fp #b" + signStr + " #b" + exponentStr + " #b" + mantissaStr + ")";
  }

  public static String generateOnes(int count) {
    return "1".repeat(count);
  }

  public static String generateZeros(int count) {
    return "0".repeat(count);
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(String pVar, FloatingPointType pType) {
    SMTLIB2Formula formula = new SMTLIB2Formula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setName(pVar);
    return formula;
  }

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
