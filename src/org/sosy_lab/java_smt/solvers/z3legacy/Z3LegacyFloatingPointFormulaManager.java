/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3legacy.Native;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

class Z3LegacyFloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Long, Long, Long, Long> {

  private static final FloatingPointType highPrec =
      FormulaType.getFloatingPointTypeFromSizesWithoutHiddenBit(15, 112);

  private final long z3context;
  private final long roundingMode;

  Z3LegacyFloatingPointFormulaManager(
      Z3LegacyFormulaCreator creator,
      Z3LegacyBitvectorFormulaManager bvMgr,
      Z3LegacyBooleanFormulaManager boolMgr,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(creator, bvMgr, boolMgr);
    z3context = creator.getEnv();
    roundingMode = getRoundingModeImpl(pFloatingPointRoundingMode);
  }

  @Override
  protected Long getDefaultRoundingMode() {
    return roundingMode;
  }

  @Override
  protected Long getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    long out;
    switch (pFloatingPointRoundingMode) {
      case NEAREST_TIES_TO_EVEN:
        out = Native.mkFpaRoundNearestTiesToEven(z3context);
        break;
      case NEAREST_TIES_AWAY:
        out = Native.mkFpaRoundNearestTiesToAway(z3context);
        break;
      case TOWARD_POSITIVE:
        out = Native.mkFpaRoundTowardPositive(z3context);
        break;
      case TOWARD_NEGATIVE:
        out = Native.mkFpaRoundTowardNegative(z3context);
        break;
      case TOWARD_ZERO:
        out = Native.mkFpaRoundTowardZero(z3context);
        break;
      default:
        throw new AssertionError("Unexpected value");
    }
    Native.incRef(z3context, out);
    return out;
  }

  private long mkFpaSort(FloatingPointType pType) {
    return getFormulaCreator().getFloatingPointType(pType);
  }

  @Override
  protected Long makeNumberImpl(double pN, FloatingPointType pType, Long pRoundingMode) {
    return makeNumberImpl(Double.toString(pN), pType, pRoundingMode);
  }

  @Override
  protected Long makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {

    final long signSort = getFormulaCreator().getBitvectorType(1);
    final long expoSort = getFormulaCreator().getBitvectorType(type.getExponentSize());
    final long mantSort =
        getFormulaCreator().getBitvectorType(type.getMantissaSizeWithoutHiddenBit());

    final long signBv = Native.mkNumeral(z3context, sign.isNegative() ? "1" : "0", signSort);
    Native.incRef(z3context, signBv);
    final long expoBv = Native.mkNumeral(z3context, exponent.toString(), expoSort);
    Native.incRef(z3context, expoBv);
    final long mantBv = Native.mkNumeral(z3context, mantissa.toString(), mantSort);
    Native.incRef(z3context, mantBv);

    final long fp = Native.mkFpaFp(z3context, signBv, expoBv, mantBv);
    Native.decRef(z3context, mantBv);
    Native.decRef(z3context, expoBv);
    Native.decRef(z3context, signBv);
    return fp;
  }

  @Override
  protected Long makeNumberAndRound(String pN, FloatingPointType pType, Long pRoundingMode) {
    // Z3 does not allow specifying a rounding mode for numerals,
    // so we create it first with a high precision and then round it down explicitly.
    if (pType.getExponentSize() <= highPrec.getExponentSize()
        || pType.getMantissaSizeWithHiddenBit() <= highPrec.getMantissaSizeWithHiddenBit()) {
      long highPrecNumber = Native.mkNumeral(z3context, pN, mkFpaSort(highPrec));
      Native.incRef(z3context, highPrecNumber);
      long smallPrecNumber =
          castToImpl(highPrecNumber, /* irrelevant: */ true, pType, pRoundingMode);
      Native.incRef(z3context, smallPrecNumber);
      long result = Native.simplify(z3context, smallPrecNumber);
      Native.decRef(z3context, highPrecNumber);
      Native.decRef(z3context, smallPrecNumber);
      return result;
    }
    return Native.mkNumeral(z3context, pN, mkFpaSort(pType));
  }

  @Override
  protected Long makeVariableImpl(String var, FloatingPointType pType) {
    return getFormulaCreator().makeVariable(mkFpaSort(pType), var);
  }

  @Override
  protected Long makePlusInfinityImpl(FloatingPointType pType) {
    return Native.mkFpaInf(z3context, mkFpaSort(pType), false);
  }

  @Override
  protected Long makeMinusInfinityImpl(FloatingPointType pType) {
    return Native.mkFpaInf(z3context, mkFpaSort(pType), true);
  }

  @Override
  protected Long makeNaNImpl(FloatingPointType pType) {
    return Native.mkFpaNan(z3context, mkFpaSort(pType));
  }

  @Override
  protected Long castToImpl(
      Long pNumber, boolean pSigned, FormulaType<?> pTargetType, Long pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      return Native.mkFpaToFpFloat(z3context, pRoundingMode, pNumber, mkFpaSort(targetType));

    } else if (pTargetType.isBitvectorType()) {
      FormulaType.BitvectorType targetType = (FormulaType.BitvectorType) pTargetType;
      if (pSigned) {
        return Native.mkFpaToSbv(z3context, pRoundingMode, pNumber, targetType.getSize());
      } else {
        return Native.mkFpaToUbv(z3context, pRoundingMode, pNumber, targetType.getSize());
      }

    } else if (pTargetType.isRationalType()) {
      return Native.mkFpaToReal(z3context, pNumber);

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  @Override
  protected Long castFromImpl(
      Long pNumber, boolean pSigned, FloatingPointType pTargetType, Long pRoundingMode) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);

    if (formulaType.isFloatingPointType()) {
      return castToImpl(pNumber, pSigned, pTargetType, pRoundingMode);

    } else if (formulaType.isBitvectorType()) {
      if (pSigned) {
        return Native.mkFpaToFpSigned(z3context, pRoundingMode, pNumber, mkFpaSort(pTargetType));
      } else {
        return Native.mkFpaToFpUnsigned(z3context, pRoundingMode, pNumber, mkFpaSort(pTargetType));
      }

    } else if (formulaType.isRationalType()) {
      return Native.mkFpaToFpReal(z3context, pRoundingMode, pNumber, mkFpaSort(pTargetType));

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  private Long genericCast(Long pNumber, FormulaType<?> pTargetType) {
    FormulaType<?> argType = getFormulaCreator().getFormulaType(pNumber);
    long castFuncDecl =
        getFormulaCreator()
            .declareUFImpl(
                "__cast_" + argType + "_to_" + pTargetType,
                toSolverType(pTargetType),
                ImmutableList.of(toSolverType(argType)));
    return Native.mkApp(z3context, castFuncDecl, 1, new long[] {pNumber});
  }

  @Override
  protected Long fromIeeeBitvectorImpl(Long pNumber, FloatingPointType pTargetType) {
    return Native.mkFpaToFpBv(z3context, pNumber, mkFpaSort(pTargetType));
  }

  @Override
  protected Long toIeeeBitvectorImpl(Long pNumber) {
    return Native.mkFpaToIeeeBv(z3context, pNumber);
  }

  @Override
  protected Long negate(Long pNumber) {
    return Native.mkFpaNeg(z3context, pNumber);
  }

  @Override
  protected Long abs(Long pNumber) {
    return Native.mkFpaAbs(z3context, pNumber);
  }

  @Override
  protected Long max(Long pNumber1, Long pNumber2) {
    return Native.mkFpaMax(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long min(Long pNumber1, Long pNumber2) {
    return Native.mkFpaMin(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long sqrt(Long pNumber, Long pRoundingMode) {
    return Native.mkFpaSqrt(z3context, pRoundingMode, pNumber);
  }

  @Override
  protected Long add(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return Native.mkFpaAdd(z3context, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long subtract(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return Native.mkFpaSub(z3context, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long multiply(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return Native.mkFpaMul(z3context, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long remainder(Long pParam1, Long pParam2) {
    return Native.mkFpaRem(z3context, pParam1, pParam2);
  }

  @Override
  protected Long divide(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return Native.mkFpaDiv(z3context, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long assignment(Long pNumber1, Long pNumber2) {
    return Native.mkEq(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long equalWithFPSemantics(Long pNumber1, Long pNumber2) {
    return Native.mkFpaEq(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long greaterThan(Long pNumber1, Long pNumber2) {
    return Native.mkFpaGt(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long greaterOrEquals(Long pNumber1, Long pNumber2) {
    return Native.mkFpaGeq(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long lessThan(Long pNumber1, Long pNumber2) {
    return Native.mkFpaLt(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long lessOrEquals(Long pNumber1, Long pNumber2) {
    return Native.mkFpaLeq(z3context, pNumber1, pNumber2);
  }

  @Override
  protected Long isNaN(Long pParam) {
    return Native.mkFpaIsNan(z3context, pParam);
  }

  @Override
  protected Long isInfinity(Long pParam) {
    return Native.mkFpaIsInfinite(z3context, pParam);
  }

  @Override
  protected Long isZero(Long pParam) {
    return Native.mkFpaIsZero(z3context, pParam);
  }

  @Override
  protected Long isSubnormal(Long pParam) {
    return Native.mkFpaIsSubnormal(z3context, pParam);
  }

  @Override
  protected Long isNormal(Long pParam) {
    return Native.mkFpaIsNormal(z3context, pParam);
  }

  @Override
  protected Long isNegative(Long pParam) {
    return Native.mkFpaIsNegative(z3context, pParam);
  }

  @Override
  protected Long round(Long pFormula, FloatingPointRoundingMode pRoundingMode) {
    return Native.mkFpaRoundToIntegral(z3context, getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
