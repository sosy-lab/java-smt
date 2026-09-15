// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import com.sri.yices.Terms;
import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

class Yices2BitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Integer, Integer, Long, Integer> {

  Yices2BitvectorFormulaManager(Yices2FormulaCreator pCreator, Yices2BooleanFormulaManager pBmgr) {
    super(pCreator, pBmgr);
  }

  @Override
  protected Integer makeBitvectorImpl(int pLength, BigInteger pI) {
    pI = transformValueToRange(pLength, pI);
    String bits = pI.toString(2);
    assert bits.length() <= pLength
        : "numeral value " + pI + " is out of range for size " + pLength;
    if (bits.length() < pLength) {
      bits = Strings.padStart(bits, pLength, '0');
    }
    Preconditions.checkArgument(bits.length() == pLength, "Bitvector has unexpected size.");
    return Terms.parseBvBin(bits);
  }

  @Override
  protected Integer toIntegerFormulaImpl(Integer bvFormula, boolean pSigned) {
    throw new UnsupportedOperationException(
        "Yices does not support making an INT formula from a BV formula as of Version 2.6.1. "
            + "Support is planned for a future release.");
  }

  @Override
  protected Integer negate(Integer pParam1) {
    return Terms.bvNeg(pParam1);
  }

  @Override
  protected Integer add(Integer pParam1, Integer pParam2) {
    return Terms.bvAdd(pParam1, pParam2);
  }

  @Override
  protected Integer subtract(Integer pParam1, Integer pParam2) {
    return Terms.bvSub(pParam1, pParam2);
  }

  @Override
  protected Integer divide(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSDiv(pParam1, pParam2);
    } else {
      return Terms.bvDiv(pParam1, pParam2);
    }
  }

  @Override
  protected Integer remainder(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSRem(pParam1, pParam2);
    } else {
      return Terms.bvRem(pParam1, pParam2);
    }
  }

  @Override
  protected Integer smodulo(Integer pParam1, Integer pParam2) {
    return Terms.bvSMod(pParam1, pParam2);
  }

  @Override
  protected Integer multiply(Integer pParam1, Integer pParam2) {
    return Terms.bvMul(pParam1, pParam2);
  }

  @Override
  protected Integer equal(Integer pParam1, Integer pParam2) {
    return Terms.bvEq(pParam1, pParam2);
  }

  @Override
  protected Integer greaterThan(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSGt(pParam1, pParam2);
    } else {
      return Terms.bvGt(pParam1, pParam2);
    }
  }

  @Override
  protected Integer greaterOrEquals(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSGe(pParam1, pParam2);
    } else {
      return Terms.bvGe(pParam1, pParam2);
    }
  }

  @Override
  protected Integer lessThan(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSLt(pParam1, pParam2);
    } else {
      return Terms.bvLt(pParam1, pParam2);
    }
  }

  @Override
  protected Integer lessOrEquals(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSLe(pParam1, pParam2);
    } else {
      return Terms.bvLe(pParam1, pParam2);
    }
  }

  @Override
  protected Integer not(Integer pParam1) {
    return Terms.bvNot(pParam1);
  }

  @Override
  protected Integer and(Integer pParam1, Integer pParam2) {
    return Terms.bvAnd(pParam1, pParam2);
  }

  @Override
  protected Integer or(Integer pParam1, Integer pParam2) {
    return Terms.bvOr(pParam1, pParam2);
  }

  @Override
  protected Integer xor(Integer pParam1, Integer pParam2) {
    return Terms.bvXor(pParam1, pParam2);
  }

  @Override
  protected Integer makeVariableImpl(int pLength, String pVar) {
    int bvType = getFormulaCreator().getBitvectorType(pLength);
    return getFormulaCreator().makeVariable(bvType, pVar);
  }

  @Override
  protected Integer shiftRight(Integer pNumber, Integer pToShift, boolean pSigned) {
    if (pSigned) {
      return Terms.bvAshr(pNumber, pToShift);
    } else {
      return Terms.bvLshr(pNumber, pToShift);
    }
  }

  @Override
  protected Integer shiftLeft(Integer pNumber, Integer pToShift) {
    return Terms.bvShl(pNumber, pToShift);
  }

  @Override
  protected Integer rotateLeftByConstant(Integer pNumber, int toRotate) {
    return Terms.bvRotateLeft(pNumber, toRotate);
  }

  @Override
  protected Integer rotateRightByConstant(Integer pNumber, int toRotate) {
    return Terms.bvRotateRight(pNumber, toRotate);
  }

  @Override
  protected Integer concat(Integer pNumber, Integer pAppend) {
    return Terms.bvConcat(pNumber, pAppend);
  }

  @Override
  protected Integer extract(Integer pNumber, int pMsb, int pLsb) {
    return Terms.bvExtract(pNumber, pLsb, pMsb);
  }

  @Override
  protected Integer extend(Integer pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return Terms.bvSignExtend(pNumber, pExtensionBits);
    } else {
      return Terms.bvZeroExtend(pNumber, pExtensionBits);
    }
  }

  @Override
  protected Integer makeBitvectorImpl(int pLength, Integer pFormula) {
    throw new UnsupportedOperationException(
        "Yices does not support making a BV formula from an INT formula as of Version 2.6.1. "
            + "Support is planned for a future release.");
  }
}
