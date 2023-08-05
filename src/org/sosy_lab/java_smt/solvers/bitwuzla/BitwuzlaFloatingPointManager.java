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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static org.sosy_lab.java_smt.solvers.bitwuzla.SWIG_BitwuzlaKind.*;

import com.microsoft.z3.Native;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Op;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaFloatingPointManager extends
                                          AbstractFloatingPointFormulaManager<Long, Long, Long, Long> {
  private final long bitwuzla;
  private final long roundingMode;
  protected BitwuzlaFloatingPointManager(FormulaCreator<Long, Long, Long, Long> pCreator, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(pCreator);
    bitwuzla = pCreator.getEnv();
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
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzla, BitwuzlaJNI.BITWUZLA_RM_RNE_get());
        break;
      case NEAREST_TIES_AWAY:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzla, BitwuzlaJNI.BITWUZLA_RM_RNA_get());
        break;
      case TOWARD_POSITIVE:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzla, BitwuzlaJNI.BITWUZLA_RM_RTP_get());
        break;
      case TOWARD_NEGATIVE:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzla, BitwuzlaJNI.BITWUZLA_RM_RTN_get());
        break;
      case TOWARD_ZERO:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzla, BitwuzlaJNI.BITWUZLA_RM_RTZ_get());
        break;
      default:
        throw new AssertionError("Unexpected value");
    }
    return out;
  }

  @Override
  protected Long makeNumberImpl(double n, FloatingPointType type, Long pFloatingPointRoundingMode) {
    return makeNumberImpl(Double.toString(n), type, pFloatingPointRoundingMode);
  }

  private long mkFpaSort(FloatingPointType pType) {
    return getFormulaCreator().getFloatingPointType(pType);
  }

  // TODO
  @Override
  protected Long makeNumberAndRound(
      String pN,
      FloatingPointType pType,
      Long pFloatingPointRoundingMode) {
    return null;
  }

  @Override
  protected Long makeVariableImpl(String pVar, FloatingPointType pType) {
    return getFormulaCreator().makeVariable(mkFpaSort(pType), pVar);
  }

  @Override
  protected Long makePlusInfinityImpl(FloatingPointType pType) {
    return BitwuzlaJNI.bitwuzla_mk_fp_pos_inf(bitwuzla, mkFpaSort(pType));
  }

  @Override
  protected Long makeMinusInfinityImpl(FloatingPointType pType) {
    return BitwuzlaJNI.bitwuzla_mk_fp_neg_inf(bitwuzla, mkFpaSort(pType));
  }

  @Override
  protected Long makeNaNImpl(FloatingPointType pType) {
    return BitwuzlaJNI.bitwuzla_mk_fp_nan(bitwuzla, mkFpaSort(pType));
  }

  @Override
  protected Long castToImpl(
      Long pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      Long pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FormulaType.FloatingPointType targetType = (FormulaType.FloatingPointType) pTargetType;
      return BitwuzlaJNI.bitwuzla_mk_term2_indexed2(bitwuzla,
          BITWUZLA_KIND_FP_TO_FP_FROM_FP.swigValue(), pRoundingMode, pNumber,
          targetType.getExponentSize(), targetType.getMantissaSize());
    } else if (pTargetType.isBitvectorType()) {
      FormulaType.BitvectorType targetType = (FormulaType.BitvectorType) pTargetType;
      if (pSigned) {
        return BitwuzlaJNI.bitwuzla_mk_term2_indexed1(bitwuzla, BITWUZLA_KIND_FP_TO_SBV.swigValue(),
            pRoundingMode, pNumber,
            targetType.getSize());
      } else {
        return BitwuzlaJNI.bitwuzla_mk_term2_indexed1(bitwuzla, BITWUZLA_KIND_FP_TO_UBV.swigValue(),
            pRoundingMode, pNumber,
            targetType.getSize());
      }
    } else {
        throw new UnsupportedOperationException("Attempted cast to an unsupported type.");
    }
  }

  //TODO, see notes
  @Override
  protected Long castFromImpl(
      Long pNumber,
      boolean pSigned,
      FloatingPointType pTargetType,
      Long pRoundingMode) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);
      if (formulaType.isFloatingPointType()) {
        return castToImpl(pNumber, pSigned, pTargetType, pRoundingMode);
      } else if (formulaType.isBitvectorType()) {
        if (pSigned) {
          return BitwuzlaJNI.bitwuzla_mk_term2_indexed2(bitwuzla,
              BITWUZLA_KIND_FP_TO_FP_FROM_SBV.swigValue()
              , roundingMode, pNumber, pTargetType.getExponentSize(),
              pTargetType.getMantissaSize() + 1);
        } else {
          return BitwuzlaJNI.bitwuzla_mk_term2_indexed2(bitwuzla,
              BITWUZLA_KIND_FP_TO_FP_FROM_UBV.swigValue()
              , roundingMode, pNumber, pTargetType.getExponentSize(),
              pTargetType.getMantissaSize() + 1);
        }

      } else {
        throw new UnsupportedOperationException("Attempted cast from an unsupported type.");
      }
    }

  @Override
  protected Long fromIeeeBitvectorImpl(Long pNumber, FloatingPointType pTargetType) {
    return BitwuzlaJNI.bitwuzla_mk_term1_indexed2(bitwuzla,
        BITWUZLA_KIND_FP_TO_FP_FROM_BV.swigValue(), pNumber,
        pTargetType.getExponentSize(), pTargetType.getMantissaSize() + 1);
  }

  // TODO Should this be to unsigned or signed BV? Is the Roundingmode correct? Is this perhaps
  // just not supported by Bitwuzla?
  @Override
  protected Long toIeeeBitvectorImpl(Long pNumber) {
    String roundingMode = BitwuzlaJNI.bitwuzla_get_rm_value(bitwuzla, pNumber);
    long pRoundingMode = getRoundingModeImpl(FloatingPointRoundingMode.valueOf(roundingMode));
    long inputBits =
        BitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(pNumber) + BitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(pNumber);
    return BitwuzlaJNI.bitwuzla_mk_term2_indexed1(bitwuzla,
        BITWUZLA_KIND_FP_TO_SBV.swigValue(),  pRoundingMode, pNumber, inputBits);
  }

  @Override
  protected Long negate(Long pParam1) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_NEG.swigValue(),
        pParam1);
  }

  @Override
  protected Long abs(Long pParam1) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,
        BITWUZLA_KIND_FP_ABS.swigValue(),
        pParam1);
  }

  @Override
  protected Long max(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        BITWUZLA_KIND_FP_MAX.swigValue(),
        pParam1, pParam2);
  }

  @Override
  protected Long min(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        BITWUZLA_KIND_FP_MIN.swigValue(),
        pParam1, pParam2);
  }

  @Override
  protected Long sqrt(Long pNumber, Long pRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        BITWUZLA_KIND_FP_SQRT.swigValue(),
        pRoundingMode, pNumber);
  }

  @Override
  protected Long add(Long pParam1, Long pParam2, Long pRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(bitwuzla,
        BITWUZLA_KIND_FP_ADD.swigValue(), pRoundingMode,
        pParam1, pParam2);
  }

  @Override
  protected Long subtract(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(bitwuzla,
        BITWUZLA_KIND_FP_SUB.swigValue(), pFloatingPointRoundingMode,
        pParam1, pParam2);
  }

  @Override
  protected Long divide(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(bitwuzla,
        BITWUZLA_KIND_FP_DIV.swigValue(), pFloatingPointRoundingMode,
        pParam1, pParam2);
  }

  @Override
  protected Long multiply(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(bitwuzla,
        BITWUZLA_KIND_FP_MUL.swigValue(), pFloatingPointRoundingMode,
        pParam1, pParam2);
  }

  @Override
  protected Long assignment(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long equalWithFPSemantics(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_FP_EQ.swigValue(), pParam1, pParam2);

  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_FP_GT.swigValue(), pParam1,
        pParam2);
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_FP_GEQ.swigValue(), pParam1,
        pParam2);
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_FP_LT.swigValue(), pParam1,
        pParam2);
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_FP_LEQ.swigValue(), pParam1,
        pParam2);
  }

  @Override
  protected Long isNaN(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_IS_NAN.swigValue(),
        pParam);
  }

  @Override
  protected Long isInfinity(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_IS_INF.swigValue(),
        pParam);
  }

  @Override
  protected Long isZero(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_IS_ZERO.swigValue(),
        pParam);
  }

  @Override
  protected Long isSubnormal(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_IS_SUBNORMAL.swigValue(),
        pParam);
  }

  @Override
  protected Long isNormal(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_IS_NORMAL.swigValue(),
        pParam);
  }

  @Override
  protected Long isNegative(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,  BITWUZLA_KIND_FP_IS_NEG.swigValue(),
        pParam);
  }

  @Override
  protected Long round(Long pFormula, FloatingPointRoundingMode pRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,  BITWUZLA_KIND_FP_IS_NAN.swigValue(),
        getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
