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
package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_cast;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_div;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_from_sbv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_from_ubv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isinf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isnan;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_isneg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_issubnormal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_iszero;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_leq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_lt;
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
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_fp_to_bv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_uf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

class Mathsat5FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Long, Long, Long, Long> {

  private final long mathsatEnv;

  private final long roundingMode;

  Mathsat5FloatingPointFormulaManager(
      Mathsat5FormulaCreator pCreator, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(pCreator);

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
  public Long makeNumberImpl(double pN, FloatingPointType pType, Long pRoundingMode) {
    if (Double.isNaN(pN)) {
      return makeNaNImpl(pType);
    } else if (Double.POSITIVE_INFINITY == pN) {
      return makePlusInfinityImpl(pType);
    } else if (Double.NEGATIVE_INFINITY == pN) {
      return makeMinusInfinityImpl(pType);
    }
    long numeral =
        msat_make_fp_rat_number(
            mathsatEnv,
            Double.toString(pN),
            pType.getExponentSize(),
            pType.getMantissaSize(),
            pRoundingMode);
    if (isNegativeZero(pN)) {
      numeral = msat_make_fp_neg(mathsatEnv, numeral);
    }
    return numeral;
  }

  private static boolean isNegativeZero(double pN) {
    return pN == 0.0 && Double.valueOf(-0.0).equals(Double.valueOf(pN));
  }

  @Override
  public Long makeNumberImpl(BigDecimal pN, FloatingPointType pType, Long pRoundingMode) {
    return makeNumberImpl(pN.toPlainString(), pType, pRoundingMode);
  }

  @Override
  protected Long makeNumberImpl(String pN, FloatingPointType pType, Long pRoundingMode) {
    try {
      return makeNumberImpl(Double.valueOf(pN), pType, pRoundingMode);
    } catch (NumberFormatException e) {
      // fallback to direct String-based method
      return msat_make_fp_rat_number(
          mathsatEnv, pN, pType.getExponentSize(), pType.getMantissaSize(), pRoundingMode);
    }
  }

  @Override
  public Long makeVariableImpl(String var, FloatingPointType type) {
    return getFormulaCreator().makeVariable(getFormulaCreator().getFloatingPointType(type), var);
  }

  @Override
  protected Long makePlusInfinityImpl(FloatingPointType type) {
    return msat_make_fp_plus_inf(mathsatEnv, type.getExponentSize(), type.getMantissaSize());
  }

  @Override
  protected Long makeMinusInfinityImpl(FloatingPointType type) {
    return msat_make_fp_minus_inf(mathsatEnv, type.getExponentSize(), type.getMantissaSize());
  }

  @Override
  protected Long makeNaNImpl(FloatingPointType type) {
    return msat_make_fp_nan(mathsatEnv, type.getExponentSize(), type.getMantissaSize());
  }

  @Override
  protected Long castToImpl(Long pNumber, FormulaType<?> pTargetType, Long pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FormulaType.FloatingPointType targetType = (FormulaType.FloatingPointType) pTargetType;
      return msat_make_fp_cast(
          mathsatEnv,
          targetType.getExponentSize(),
          targetType.getMantissaSize(),
          pRoundingMode,
          pNumber);

    } else if (pTargetType.isBitvectorType()) {
      FormulaType.BitvectorType targetType = (FormulaType.BitvectorType) pTargetType;
      return msat_make_fp_to_bv(mathsatEnv, targetType.getSize(), pRoundingMode, pNumber);

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  @Override
  protected Long castFromImpl(
      Long pNumber, boolean signed, FloatingPointType pTargetType, Long pRoundingMode) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);

    if (formulaType.isFloatingPointType()) {
      return castToImpl(pNumber, pTargetType, pRoundingMode);

    } else if (formulaType.isBitvectorType()) {
      if (signed) {
        return msat_make_fp_from_sbv(
            mathsatEnv,
            pTargetType.getExponentSize(),
            pTargetType.getMantissaSize(),
            pRoundingMode,
            pNumber);
      } else {
        return msat_make_fp_from_ubv(
            mathsatEnv,
            pTargetType.getExponentSize(),
            pTargetType.getMantissaSize(),
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
    return Mathsat5NativeApi.msat_make_fp_from_ieeebv(
        mathsatEnv, pTargetType.getExponentSize(), pTargetType.getMantissaSize(), pNumber);
  }

  @Override
  protected Long toIeeeBitvectorImpl(Long pNumber) {
    return Mathsat5NativeApi.msat_make_fp_as_ieeebv(mathsatEnv, pNumber);
  }

  @Override
  public Long negate(Long pNumber) {
    return msat_make_fp_neg(mathsatEnv, pNumber);
  }

  @Override
  public Long add(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_plus(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  public Long subtract(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_minus(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
  }

  @Override
  public Long multiply(Long pNumber1, Long pNumber2, Long pRoundingMode) {
    return msat_make_fp_times(mathsatEnv, pRoundingMode, pNumber1, pNumber2);
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
  public Long equalWithFPSemantics(Long pNumber1, Long pNumber2) {
    return msat_make_fp_equal(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  public Long greaterThan(Long pNumber1, Long pNumber2) {
    return lessThan(pNumber2, pNumber1);
  }

  @Override
  public Long greaterOrEquals(Long pNumber1, Long pNumber2) {
    return lessOrEquals(pNumber2, pNumber1);
  }

  @Override
  public Long lessThan(Long pNumber1, Long pNumber2) {
    return msat_make_fp_lt(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  public Long lessOrEquals(Long pNumber1, Long pNumber2) {
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
  protected Long isNegative(Long pParam) {
    return msat_make_fp_isneg(mathsatEnv, pParam);
  }

  @Override
  protected Long round(Long pFormula, FloatingPointRoundingMode pRoundingMode) {
    return msat_make_fp_round_to_int(mathsatEnv, getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
