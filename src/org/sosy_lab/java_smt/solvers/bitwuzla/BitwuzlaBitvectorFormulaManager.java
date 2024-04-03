// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Long, Long, Long, BitwuzlaDeclaration> {

  protected BitwuzlaBitvectorFormulaManager(
      FormulaCreator<Long, Long, Long, BitwuzlaDeclaration> pCreator,
      AbstractBooleanFormulaManager<Long, Long, Long, BitwuzlaDeclaration> pBmgr) {
    super(pCreator, pBmgr);
  }

  @Override
  protected Long makeBitvectorImpl(int length, Long pParam1) {
    throw new UnsupportedOperationException("Bitwuzla does not support INT theory");
  }

  @Override
  protected Long makeBitvectorImpl(int length, BigInteger pI) {
    pI = transformValueToRange(length, pI);
    long sort = BitwuzlaJNI.bitwuzla_mk_bv_sort(length);
    return BitwuzlaJNI.bitwuzla_mk_bv_value(sort, pI.toString(), 10);
  }

  @Override
  protected Long toIntegerFormulaImpl(Long pI, boolean signed) {
    throw new UnsupportedOperationException("BV to INT conversion is not supported.");
  }

  @Override
  protected Long negate(Long pParam1) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BitwuzlaKind.BITWUZLA_KIND_BV_NOT.swigValue(), pParam1);
  }

  @Override
  protected Long add(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_ADD.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long subtract(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_SUB.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long divide(Long pParam1, Long pParam2, boolean signed) {
    if (signed) {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_SDIV.swigValue(), pParam1, pParam2);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_UDIV.swigValue(), pParam1, pParam2);
    }
  }

  @Override
  protected Long remainder(Long pParam1, Long pParam2, boolean signed) {
    BitwuzlaKind kind =
        signed ? BitwuzlaKind.BITWUZLA_KIND_BV_SREM : BitwuzlaKind.BITWUZLA_KIND_BV_UREM;
    return BitwuzlaJNI.bitwuzla_mk_term2(kind.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long smodulo(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_SMOD.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long multiply(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_MUL.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long equal(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2, boolean signed) {
    if (signed) {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_SGT.swigValue(), pParam1, pParam2);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_UGT.swigValue(), pParam1, pParam2);
    }
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2, boolean signed) {
    if (signed) {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_SGE.swigValue(), pParam1, pParam2);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_UGE.swigValue(), pParam1, pParam2);
    }
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2, boolean signed) {
    if (signed) {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_SLT.swigValue(), pParam1, pParam2);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_ULT.swigValue(), pParam1, pParam2);
    }
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2, boolean signed) {
    if (signed) {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_SLE.swigValue(), pParam1, pParam2);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_ULE.swigValue(), pParam1, pParam2);
    }
  }

  @Override
  protected Long not(Long pParam1) {
    return BitwuzlaJNI.bitwuzla_mk_term1(BitwuzlaKind.BITWUZLA_KIND_BV_NOT.swigValue(), pParam1);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_AND.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_OR.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_XOR.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long makeVariableImpl(int pLength, String pVar) {
    long sort = BitwuzlaJNI.bitwuzla_mk_bv_sort(pLength);
    return getFormulaCreator().makeVariable(sort, pVar);
  }

  @Override
  protected Long shiftRight(Long pNumber, Long toShift, boolean signed) {
    if (signed) {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_ASHR.swigValue(), pNumber, toShift);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term2(
          BitwuzlaKind.BITWUZLA_KIND_BV_SHR.swigValue(), pNumber, toShift);
    }
  }

  @Override
  protected Long shiftLeft(Long pNumber, Long toShift) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_SHL.swigValue(), pNumber, toShift);
  }

  @Override
  protected Long concat(Long number, Long pAppend) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT.swigValue(), number, pAppend);
  }

  @Override
  protected Long extract(Long pNumber, int pMsb, int pLsb) {
    return BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
        BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), pNumber, pMsb, pLsb);
  }

  @Override
  protected Long extend(Long pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return BitwuzlaJNI.bitwuzla_mk_term1_indexed1(
          BitwuzlaKind.BITWUZLA_KIND_BV_SIGN_EXTEND.swigValue(), pNumber, pExtensionBits);
    } else {
      return BitwuzlaJNI.bitwuzla_mk_term1_indexed1(
          BitwuzlaKind.BITWUZLA_KIND_BV_ZERO_EXTEND.swigValue(), pNumber, pExtensionBits);
    }
  }
}
