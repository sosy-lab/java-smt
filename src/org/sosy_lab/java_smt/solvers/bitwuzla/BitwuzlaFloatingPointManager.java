// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_EQUAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_ABS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_ADD;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_DIV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_EQUAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_GEQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_GT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_INF;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_NAN;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_NEG;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_NORMAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_SUBNORMAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_ZERO;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_LEQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_LT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_MAX;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_MIN;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_MUL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_NEG;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_RTI;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_SQRT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_SUB;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_BV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_FP;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_SBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_UBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_UBV;

import java.math.BigDecimal;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaFloatingPointManager
    extends AbstractFloatingPointFormulaManager<Long, Long, Long, BitwuzlaDeclaration> {
  // private final long bitwuzla;
  private final BitwuzlaFormulaCreator bitwuzlaCreator;
  private final long roundingMode;

  protected BitwuzlaFloatingPointManager(
      FormulaCreator<Long, Long, Long, BitwuzlaDeclaration> pCreator,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(pCreator);
    bitwuzlaCreator = (BitwuzlaFormulaCreator) pCreator;
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
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RNE_get());
        break;
      case NEAREST_TIES_AWAY:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RNA_get());
        break;
      case TOWARD_POSITIVE:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RTP_get());
        break;
      case TOWARD_NEGATIVE:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RTN_get());
        break;
      case TOWARD_ZERO:
        out = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RTZ_get());
        break;
      default:
        throw new AssertionError("Unexpected value");
    }
    return out;
  }

  @Override
  public Long makeNumberImpl(
      Rational n, FormulaType.FloatingPointType type, Long pFloatingPointRoundingMode) {
    BigDecimal num = new BigDecimal(n.getNum());
    BigDecimal den = new BigDecimal(n.getDen());
    return makeNumberImpl(num.divide(den).toString(), type, pFloatingPointRoundingMode);
  }

  @Override
  protected Long makeNumberImpl(double n, FloatingPointType type, Long pFloatingPointRoundingMode) {
    return makeNumberImpl(String.valueOf(n), type, pFloatingPointRoundingMode);
  }

  private long mkFpaSort(FloatingPointType pType) {
    return getFormulaCreator().getFloatingPointType(pType);
  }

  @Override
  protected Long makeNumberAndRound(
      String pN, FloatingPointType pType, Long pFloatingPointRoundingMode) {
    Double.parseDouble(pN); // Will throw an exception if the string is not a valid float
    return BitwuzlaJNI.bitwuzla_mk_fp_from_real(mkFpaSort(pType), pFloatingPointRoundingMode, pN);
  }

  @Override
  protected Long makeVariableImpl(String pVar, FloatingPointType pType) {
    return getFormulaCreator().makeVariable(mkFpaSort(pType), pVar);
  }

  @Override
  protected Long makePlusInfinityImpl(FloatingPointType pType) {
    return BitwuzlaJNI.bitwuzla_mk_fp_pos_inf(mkFpaSort(pType));
  }

  @Override
  protected Long makeMinusInfinityImpl(FloatingPointType pType) {
    return BitwuzlaJNI.bitwuzla_mk_fp_neg_inf(mkFpaSort(pType));
  }

  @Override
  protected Long makeNaNImpl(FloatingPointType pType) {
    return BitwuzlaJNI.bitwuzla_mk_fp_nan(mkFpaSort(pType));
  }

  @Override
  protected Long castToImpl(
      Long pNumber, boolean pSigned, FormulaType<?> pTargetType, Long pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FormulaType.FloatingPointType targetType = (FormulaType.FloatingPointType) pTargetType;
      return BitwuzlaJNI.bitwuzla_mk_term2_indexed2(
          BITWUZLA_KIND_FP_TO_FP_FROM_FP.swigValue(),
          pRoundingMode,
          pNumber,
          targetType.getExponentSize(),
          targetType.getMantissaSize() + 1);
    } else if (pTargetType.isBitvectorType()) {
      FormulaType.BitvectorType targetType = (FormulaType.BitvectorType) pTargetType;
      if (pSigned) {
        return BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BITWUZLA_KIND_FP_TO_SBV.swigValue(), pRoundingMode, pNumber, targetType.getSize());
      } else {
        return BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BITWUZLA_KIND_FP_TO_UBV.swigValue(), pRoundingMode, pNumber, targetType.getSize());
      }
    } else {
      throw new UnsupportedOperationException("Attempted cast to an unsupported type.");
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
        return BitwuzlaJNI.bitwuzla_mk_term2_indexed2(
            BITWUZLA_KIND_FP_TO_FP_FROM_SBV.swigValue(),
            roundingMode,
            pNumber,
            pTargetType.getExponentSize(),
            pTargetType.getMantissaSize() + 1);
      } else {
        return BitwuzlaJNI.bitwuzla_mk_term2_indexed2(
            BITWUZLA_KIND_FP_TO_FP_FROM_UBV.swigValue(),
            roundingMode,
            pNumber,
            pTargetType.getExponentSize(),
            pTargetType.getMantissaSize() + 1);
      }

    } else {
      throw new UnsupportedOperationException("Attempted cast from an unsupported type.");
    }
  }

  @Override
  protected Long fromIeeeBitvectorImpl(Long pNumber, FloatingPointType pTargetType) {
    return BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
        BITWUZLA_KIND_FP_TO_FP_FROM_BV.swigValue(),
        pNumber,
        pTargetType.getExponentSize(),
        pTargetType.getMantissaSize() + 1);
  }

  @Override
  protected Long toIeeeBitvectorImpl(Long pNumber) {
    long sizeExp = BitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(pNumber);
    long sizeSig = BitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(pNumber);

    long bvSort = BitwuzlaJNI.bitwuzla_mk_bv_sort(sizeExp + sizeSig);

    long bvVar = BitwuzlaJNI.bitwuzla_mk_const(bvSort, "");
    long equal = BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
        BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
            BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_BV.swigValue(),
            bvVar, sizeExp,
            sizeSig),
        pNumber);

    bitwuzlaCreator.addVariableCast(equal);
    return bvVar;
  }

  @Override
  protected Long negate(Long pParam1) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_NEG.swigValue(), pParam1);
  }

  @Override
  protected Long abs(Long pParam1) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_ABS.swigValue(), pParam1);
  }

  @Override
  protected Long max(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_MAX.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long min(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_MIN.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long sqrt(Long pNumber, Long pRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_SQRT.swigValue(), pRoundingMode, pNumber);
  }

  @Override
  protected Long add(Long pParam1, Long pParam2, Long pRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(
        BITWUZLA_KIND_FP_ADD.swigValue(), pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Long subtract(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(
        BITWUZLA_KIND_FP_SUB.swigValue(), pFloatingPointRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Long divide(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(
        BITWUZLA_KIND_FP_DIV.swigValue(), pFloatingPointRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Long multiply(Long pParam1, Long pParam2, Long pFloatingPointRoundingMode) {
    return BitwuzlaJNI.bitwuzla_mk_term3(
        BITWUZLA_KIND_FP_MUL.swigValue(), pFloatingPointRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Long assignment(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long equalWithFPSemantics(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_EQUAL.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_GT.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_GEQ.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_LT.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_LEQ.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long isNaN(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_IS_NAN.swigValue(), pParam);
  }

  @Override
  protected Long isInfinity(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_IS_INF.swigValue(), pParam);
  }

  @Override
  protected Long isZero(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_IS_ZERO.swigValue(), pParam);
  }

  @Override
  protected Long isSubnormal(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_IS_SUBNORMAL.swigValue(), pParam);
  }

  @Override
  protected Long isNormal(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_IS_NORMAL.swigValue(), pParam);
  }

  @Override
  protected Long isNegative(Long pParam) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BITWUZLA_KIND_FP_IS_NEG.swigValue(), pParam);
  }

  @Override
  protected Long round(Long pFormula, FloatingPointRoundingMode pRoundingMode) {
    long rm = getRoundingModeImpl(pRoundingMode);
    return BitwuzlaJNI.bitwuzla_mk_term2(BITWUZLA_KIND_FP_RTI.swigValue(), rm, pFormula);
  }
}
