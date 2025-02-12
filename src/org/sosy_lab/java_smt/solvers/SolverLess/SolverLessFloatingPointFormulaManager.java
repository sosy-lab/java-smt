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

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigDecimal;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.solvers.SolverLess.DummyType.Type;

public class SolverLessFloatingPointFormulaManager extends
                                                   AbstractFloatingPointFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFloatingPointFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }

  @Override
  protected DummyFormula getDefaultRoundingMode() {
    return new DummyFormula(new DummyType(FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN));
  }

  @Override
  protected DummyFormula getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return new DummyFormula(new DummyType(pFloatingPointRoundingMode));
  }

  @Override
  protected DummyFormula makeNumberImpl(
      double n,
      FloatingPointType type,
      DummyFormula pFloatingPointRoundingMode) {
    String binaryRepresentation = convertToSMTLibBinary(n, type);
    DummyFormula formula = new DummyFormula(new DummyType(type.getExponentSize(),
        type.getMantissaSize(), pFloatingPointRoundingMode.getFormulaType().getRoundingMode()));
    formula.setRepresentation(binaryRepresentation);
    return formula;
  }

  @Override
  protected DummyFormula makeNumberAndRound(
      String pN, FloatingPointType pType, DummyFormula pFloatingPointRoundingMode) {
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
      throw new IllegalArgumentException("Unsupported number type: " + pN.getClass().getSimpleName());
    }
  }

  @Override
  protected DummyFormula makePlusInfinityImpl(FloatingPointType pType) {
    DummyFormula formula = new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setRepresentation("(fp #b0 #b" + generateOnes(pType.getExponentSize()) + " #b" + generateZeros(pType.getMantissaSize() - 1) + ")");
    return formula;
  }

  @Override
  protected DummyFormula makeMinusInfinityImpl(FloatingPointType pType) {
    DummyFormula formula = new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setRepresentation("(fp #b1 #b" + generateOnes(pType.getExponentSize()) + " #b" + generateZeros(pType.getMantissaSize() - 1) + ")");
    return formula;
  }

  @Override
  protected DummyFormula makeNaNImpl(FloatingPointType pType) {
    DummyFormula formula = new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setRepresentation("(fp #b0 #b" + generateOnes(pType.getExponentSize()) + " #b1" + generateZeros(pType.getMantissaSize() - 2) + ")");
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
      signBit = (bits >>> 31) & 1; //fill it with zros from the left until only the 1 or 0 is left
      exponentBits = (bits >>> mantissaSize) & ((1 << exponentSize) - 1);
      mantissaBits = bits & ((1 << mantissaSize) - 1);
    } else if (exponentSize == 11 && mantissaSize == 52) {
      long bits = Double.doubleToRawLongBits(value);
      signBit = (int) ((bits >>> 63) & 1);
      exponentBits = (int) ((bits >>> mantissaSize) & ((1L << exponentSize) - 1));
      mantissaBits = (int) (bits & ((1L << mantissaSize) - 1));
    } else {
      throw new IllegalArgumentException("Unsupported FloatingPointType: " + exponentSize + ", " + mantissaSize);
    }
    String signStr = Integer.toBinaryString(signBit);
    String exponentStr = String.format("%" + exponentSize + "s", Integer.toBinaryString(exponentBits)).replace(' ', '0');
    String mantissaStr = String.format("%" + mantissaSize + "s", Integer.toBinaryString(mantissaBits)).replace(' ', '0');

    return "(fp #b" + signStr + " #b" + exponentStr + " #b" + mantissaStr + ")";
  }


  public static String generateOnes(int count) {
    return "1".repeat(count);
  }

  public static String generateZeros(int count) {
    return "0".repeat(count);
  }




  @Override
  protected DummyFormula makeVariableImpl(String pVar, FloatingPointType pType) {
    DummyFormula formula = new DummyFormula(pType.getExponentSize(), pType.getMantissaSize());
    formula.setName(pVar);
    return formula;
  }



  @Override
  protected DummyFormula castToImpl(
      DummyFormula pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      DummyFormula pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      return new DummyFormula(targetType.getExponentSize(), targetType.getMantissaSize());
    }
    if (pTargetType.isIntegerType()) {
      return new DummyFormula(new DummyType(Type.INTEGER));
    }
    if (pTargetType.isBitvectorType()) {
      BitvectorType targetType = (BitvectorType) pTargetType;
      return new DummyFormula(targetType.getSize());
    }
    if (pTargetType.isRationalType()) {
      return new DummyFormula(new DummyType(Type.RATIONAL));
    }
    return null;
  }

  @Override
  protected DummyFormula castFromImpl(
      DummyFormula pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      DummyFormula pRoundingMode) {
    return new DummyFormula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected DummyFormula fromIeeeBitvectorImpl(
      DummyFormula pNumber,
      FloatingPointType pTargetType) {
    return new DummyFormula(pTargetType.getExponentSize(), pTargetType.getMantissaSize());
  }

  @Override
  protected DummyFormula toIeeeBitvectorImpl(DummyFormula pNumber) {
    return new DummyFormula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected DummyFormula negate(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula abs(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula max(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula min(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula sqrt(DummyFormula pNumber, DummyFormula pRoundingMode) {
    return new DummyFormula(pNumber.getExponent(), pNumber.getMantissa());
  }

  @Override
  protected DummyFormula add(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula subtract(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula divide(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula multiply(
      DummyFormula pParam1,
      DummyFormula pParam2,
      DummyFormula pFloatingPointRoundingMode) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula assignment(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(pParam1.getExponent(), pParam1.getMantissa());
  }

  @Override
  protected DummyFormula equalWithFPSemantics(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula greaterOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula isNaN(DummyFormula pParam) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula isInfinity(DummyFormula pParam) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula isZero(DummyFormula pParam) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula isSubnormal(DummyFormula pParam) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula isNormal(DummyFormula pParam) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula isNegative(DummyFormula pParam) {
    return new DummyFormula(new DummyType(Type.BOOLEAN));
  }

  @Override
  protected DummyFormula round(DummyFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return new DummyFormula(pFormula.getExponent(), pFormula.getMantissa());
  }
}


