// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_abs;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_bits_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_cast;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_div;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_from_sbv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_from_ubv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isinf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isnan;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isneg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isnormal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_issubnormal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_iszero;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_leq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_lt;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_max;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_min;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_minus;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_minus_inf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_nan;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_neg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_plus;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_plus_inf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_rat_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_round_to_int;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_roundingmode_minus_inf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_roundingmode_nearest_even;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_roundingmode_plus_inf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_roundingmode_zero;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_sqrt;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_to_sbv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_to_ubv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_uf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

class Mathsat5FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Long, Long, Long, Long> {

  private final long mathsatEnv;

  private final long roundingMode;

  Mathsat5FloatingPointFormulaManager(
      Mathsat5FormulaCreator pCreator,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      Mathsat5BitvectorFormulaManager pBvFormulaManager) {
    super(pCreator, pBvFormulaManager);

    mathsatEnv = pCreator.getEnv();
    roundingMode = getRoundingModeImpl(pFloatingPointRoundingMode);
  }

  @Override
  protected Long getDefaultRoundingMode() {
    return roundingMode;
  }

  @Override
  protected Long getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    switch (pFloatingPointRoundingMode) {
      case NEAREST_TIES_TO_EVEN:
        return msat_make_fp_roundingmode_nearest_even(mathsatEnv);
      case NEAREST_TIES_AWAY:
        throw new IllegalArgumentException(
            "Rounding mode NEAREST_TIES_AWAY is not supported by Mathsat5");
      case TOWARD_POSITIVE:
        return msat_make_fp_roundingmode_plus_inf(mathsatEnv);
      case TOWARD_NEGATIVE:
        return msat_make_fp_roundingmode_minus_inf(mathsatEnv);
      case TOWARD_ZERO:
        return msat_make_fp_roundingmode_zero(mathsatEnv);
      default:
        throw new AssertionError("Unexpected branch");
    }
  }

  @Override
  protected Long makeNumberImpl(double pN, FloatingPointType pType, Long pRoundingMode) {
    return makeNumberImpl(Double.toString(pN), pType, pRoundingMode);
  }

  @Override
  protected Long makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    final String signStr = sign.isNegative() ? "1" : "0";
    final String exponentStr = getBvRepresentation(exponent, type.getExponentSize());
    // MathSAT5 expects the mantissa to not include the hidden bit
    final String mantissaStr =
        getBvRepresentation(mantissa, type.getMantissaSizeWithoutHiddenBit());
    final String bitvecForm = signStr + exponentStr + mantissaStr;
    final BigInteger bitvecValue = new BigInteger(bitvecForm, 2);
    return msat_make_fp_bits_number(
        mathsatEnv,
        bitvecValue.toString(),
        type.getExponentSize(),
        type.getMantissaSizeWithoutHiddenBit());
  }

  @Override
  protected Long makeNumberAndRound(String pN, FloatingPointType pType, Long pRoundingMode) {
    try {
      if (isNegativeZero(Double.valueOf(pN))) {
        // MathSAT5 expects the mantissa to not include the hidden bit
        return msat_make_fp_neg(
            mathsatEnv,
            msat_make_fp_rat_number(
                mathsatEnv,
                "0",
                pType.getExponentSize(),
                pType.getMantissaSizeWithoutHiddenBit(),
                pRoundingMode));
      }
    } catch (NumberFormatException e) {
      // ignore and fallback to floating point from rational numbers
    }
    // MathSAT5 expects the mantissa to not include the hidden bit
    return msat_make_fp_rat_number(
        mathsatEnv,
        pN,
        pType.getExponentSize(),
        pType.getMantissaSizeWithoutHiddenBit(),
        pRoundingMode);
  }

  @Override
  protected Long makeVariableImpl(String var, FloatingPointType type) {
    return getFormulaCreator().makeVariable(getFormulaCreator().getFloatingPointType(type), var);
  }

  @Override
  protected Long makePlusInfinityImpl(FloatingPointType type) {
    // MathSAT5 expects the mantissa to not include the hidden bit
    return msat_make_fp_plus_inf(
        mathsatEnv, type.getExponentSize(), type.getMantissaSizeWithoutHiddenBit());
  }

  @Override
  protected Long makeMinusInfinityImpl(FloatingPointType type) {
    // MathSAT5 expects the mantissa to not include the hidden bit
    return msat_make_fp_minus_inf(
        mathsatEnv, type.getExponentSize(), type.getMantissaSizeWithoutHiddenBit());
  }

  @Override
  protected Long makeNaNImpl(FloatingPointType type) {
    // MathSAT5 expects the mantissa to not include the hidden bit
    return msat_make_fp_nan(
        mathsatEnv, type.getExponentSize(), type.getMantissaSizeWithoutHiddenBit());
  }

  @Override
  protected Long castToImpl(
      Long pNumber, boolean pSigned, FormulaType<?> pTargetType, Long pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FormulaType.FloatingPointType targetType = (FormulaType.FloatingPointType) pTargetType;
      // MathSAT5 expects the mantissa to not include the hidden bit
      return msat_make_fp_cast(
          mathsatEnv,
          targetType.getExponentSize(),
          targetType.getMantissaSizeWithoutHiddenBit(),
          pRoundingMode,
          pNumber);

    } else if (pTargetType.isBitvectorType()) {
      FormulaType.BitvectorType targetType = (FormulaType.BitvectorType) pTargetType;
      if (pSigned) {
        return msat_make_fp_to_sbv(mathsatEnv, targetType.getSize(), pRoundingMode, pNumber);
      } else {
        return msat_make_fp_to_ubv(mathsatEnv, targetType.getSize(), pRoundingMode, pNumber);
      }

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
      // MathSAT5 expects the mantissa to not include the hidden bit
      if (pSigned) {
        return msat_make_fp_from_sbv(
            mathsatEnv,
            pTargetType.getExponentSize(),
            pTargetType.getMantissaSizeWithoutHiddenBit(),
            pRoundingMode,
            pNumber);
      } else {
        return msat_make_fp_from_ubv(
            mathsatEnv,
            pTargetType.getExponentSize(),
            pTargetType.getMantissaSizeWithoutHiddenBit(),
            pRoundingMode,
            pNumber);
      }

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  private Long genericCast(Long pNumber, FormulaType<?> pTargetType) {
    long msatArgType = msat_term_get_type(pNumber);
    FormulaType<?> argType = getFormulaCreator().getFormulaType(pNumber);
    long castFuncDecl =
        getFormulaCreator()
            .declareUFImpl(
                "__cast_" + argType + "_to_" + pTargetType,
                toSolverType(pTargetType),
                ImmutableList.of(msatArgType));
    return msat_make_uf(mathsatEnv, castFuncDecl, new long[] {pNumber});
  }

  @Override
  protected Long fromIeeeBitvectorImpl(Long pNumber, FloatingPointType pTargetType) {
    // MathSAT5 expects the mantissa to not include the hidden bit
    return Mathsat5NativeApi.msat_make_fp_from_ieeebv(
        mathsatEnv,
        pTargetType.getExponentSize(),
        pTargetType.getMantissaSizeWithoutHiddenBit(),
        pNumber);
  }

  @Override
  protected Long toIeeeBitvectorImpl(Long pNumber) {
    return Mathsat5NativeApi.msat_make_fp_as_ieeebv(mathsatEnv, pNumber);
  }

  @Override
  protected Long negate(Long pNumber) {
    return msat_make_fp_neg(mathsatEnv, pNumber);
  }

  @Override
  protected Long abs(Long pNumber) {
    return msat_make_fp_abs(mathsatEnv, pNumber);
  }

  @Override
  protected Long max(Long pNumber1, Long pNumber2) {
    return msat_make_fp_max(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long min(Long pNumber1, Long pNumber2) {
    return msat_make_fp_min(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long sqrt(Long pNumber, Long pRoundingMode) {
    return msat_make_fp_sqrt(mathsatEnv, pRoundingMode, pNumber);
  }

  @Override
  protected Long add(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_plus(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long subtract(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_minus(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long multiply(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_times(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long remainder(Long pParam1, Long pParam2) {
    throw new UnsupportedOperationException("MathSAT5 does not implement fp.rem");
  }

  @Override
  protected Long divide(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_div(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  protected Long assignment(Long pNumber1, Long pNumber2) {
    return msat_make_equal(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long equalWithFPSemantics(Long pNumber1, Long pNumber2) {
    return msat_make_fp_equal(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long greaterThan(Long pNumber1, Long pNumber2) {
    return lessThan(pNumber2, pNumber1);
  }

  @Override
  protected Long greaterOrEquals(Long pNumber1, Long pNumber2) {
    return lessOrEquals(pNumber2, pNumber1);
  }

  @Override
  protected Long lessThan(Long pNumber1, Long pNumber2) {
    return msat_make_fp_lt(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long lessOrEquals(Long pNumber1, Long pNumber2) {
    return msat_make_fp_leq(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  protected Long isNaN(Long pParam) {
    return msat_make_fp_isnan(mathsatEnv, pParam);
  }

  @Override
  protected Long isInfinity(Long pParam) {
    return msat_make_fp_isinf(mathsatEnv, pParam);
  }

  @Override
  protected Long isZero(Long pParam) {
    return msat_make_fp_iszero(mathsatEnv, pParam);
  }

  @Override
  protected Long isSubnormal(Long pParam) {
    return msat_make_fp_issubnormal(mathsatEnv, pParam);
  }

  @Override
  protected Long isNormal(Long pParam) {
    return msat_make_fp_isnormal(mathsatEnv, pParam);
  }

  @Override
  protected Long isNegative(Long pParam) {
    return msat_make_fp_isneg(mathsatEnv, pParam);
  }

  @Override
  protected Long round(Long pFormula, FloatingPointRoundingMode pRoundingMode) {
    return msat_make_fp_round_to_int(mathsatEnv, getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
