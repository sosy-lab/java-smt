// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvadd;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvand2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvashr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconcat2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvdiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bveq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvextract;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvge_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvgt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvle_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvlshr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvlt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvmul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvneg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvnot;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvor2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvrem;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsdiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsge_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsgt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvshl;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsle_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvslt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsrem;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsub;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvxor2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_bvbin;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rotate_left;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rotate_right;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sign_extend;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_zero_extend;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

public class Yices2BitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2BitvectorFormulaManager(
      Yices2FormulaCreator pCreator, Yices2BooleanFormulaManager pBmgr) {
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
    return yices_parse_bvbin(bits);
  }

  @Override
  protected Integer toIntegerFormulaImpl(Integer bvFormula, boolean pSigned) {
    throw new UnsupportedOperationException(
        "Yices does not support making an INT formula from a BV formula as of Version 2.6.1. "
            + "Support is planned for a future release.");
  }

  @Override
  protected Integer negate(Integer pParam1) {
    return yices_bvneg(pParam1);
  }

  @Override
  protected Integer add(Integer pParam1, Integer pParam2) {
    return yices_bvadd(pParam1, pParam2);
  }

  @Override
  protected Integer subtract(Integer pParam1, Integer pParam2) {
    return yices_bvsub(pParam1, pParam2);
  }

  @Override
  protected Integer divide(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return yices_bvsdiv(pParam1, pParam2);
    } else {
      return yices_bvdiv(pParam1, pParam2);
    }
  }

  @Override
  protected Integer modulo(Integer pParam1, Integer pParam2, boolean pSigned) {
    // TODO Correct Methods?
    if (pSigned) {
      return yices_bvsrem(pParam1, pParam2);
    } else {
      return yices_bvrem(pParam1, pParam2);
    }
  }

  @Override
  protected Integer multiply(Integer pParam1, Integer pParam2) {
    return yices_bvmul(pParam1, pParam2);
  }

  @Override
  protected Integer equal(Integer pParam1, Integer pParam2) {
    return yices_bveq_atom(pParam1, pParam2);
  }

  @Override
  protected Integer greaterThan(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return yices_bvsgt_atom(pParam1, pParam2);
    } else {
      return yices_bvgt_atom(pParam1, pParam2);
    }
  }

  @Override
  protected Integer greaterOrEquals(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return yices_bvsge_atom(pParam1, pParam2);
    } else {
      return yices_bvge_atom(pParam1, pParam2);
    }
  }

  @Override
  protected Integer lessThan(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return yices_bvslt_atom(pParam1, pParam2);
    } else {
      return yices_bvlt_atom(pParam1, pParam2);
    }
  }

  @Override
  protected Integer lessOrEquals(Integer pParam1, Integer pParam2, boolean pSigned) {
    if (pSigned) {
      return yices_bvsle_atom(pParam1, pParam2);
    } else {
      return yices_bvle_atom(pParam1, pParam2);
    }
  }

  @Override
  protected Integer not(Integer pParam1) {
    return yices_bvnot(pParam1);
  }

  @Override
  protected Integer and(Integer pParam1, Integer pParam2) {
    return yices_bvand2(pParam1, pParam2);
  }

  @Override
  protected Integer or(Integer pParam1, Integer pParam2) {
    return yices_bvor2(pParam1, pParam2);
  }

  @Override
  protected Integer xor(Integer pParam1, Integer pParam2) {
    return yices_bvxor2(pParam1, pParam2);
  }

  @Override
  protected Integer makeVariableImpl(int pLength, String pVar) {
    int bvType = getFormulaCreator().getBitvectorType(pLength);
    return getFormulaCreator().makeVariable(bvType, pVar);
  }

  @Override
  protected Integer shiftRight(Integer pNumber, Integer pToShift, boolean pSigned) {
    if (pSigned) {
      return yices_bvashr(pNumber, pToShift);
    } else {
      return yices_bvlshr(pNumber, pToShift);
    }
  }

  @Override
  protected Integer shiftLeft(Integer pNumber, Integer pToShift) {
    return yices_bvshl(pNumber, pToShift);
  }

  @Override
  protected Integer rotateLeftByConstant(Integer pNumber, int toRotate) {
    return yices_rotate_left(pNumber, toRotate);
  }

  @Override
  protected Integer rotateRightByConstant(Integer pNumber, int toRotate) {
    return yices_rotate_right(pNumber, toRotate);
  }

  @Override
  protected Integer rotateRight(Integer pNumber, Integer toRotate) {
    // Yices2 does not support non-literal rotation, so we rewrite it to (bvor (bvlshr pNumber
    // toRotate) (bvshl pNumber (bvsub size toRotate)))
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(pNumber)).getSize();
    final Integer size = this.makeBitvectorImpl(bitsize, bitsize);
    final Integer toRotateInRange = yices_bvrem(toRotate, size);
    return or(
        shiftRight(pNumber, toRotateInRange, false),
        shiftLeft(pNumber, subtract(size, toRotateInRange)));
  }

  @Override
  protected Integer rotateLeft(Integer pNumber, Integer toRotate) {
    // Yices2 does not support non-literal rotation, so we rewrite it to (bvor (bvshl pNumber
    // toRotate) (bvlshr pNumber (bvsub size toRotate)))
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(pNumber)).getSize();
    final Integer size = this.makeBitvectorImpl(bitsize, bitsize);
    final Integer toRotateInRange = yices_bvrem(toRotate, size);
    return or(
        shiftLeft(pNumber, toRotateInRange),
        shiftRight(pNumber, subtract(size, toRotateInRange), false));
  }

  @Override
  protected Integer concat(Integer pNumber, Integer pAppend) {
    return yices_bvconcat2(pNumber, pAppend);
  }

  @Override
  protected Integer extract(Integer pNumber, int pMsb, int pLsb) {
    return yices_bvextract(pNumber, pLsb, pMsb);
  }

  @Override
  protected Integer extend(Integer pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return yices_sign_extend(pNumber, pExtensionBits);
    } else {
      return yices_zero_extend(pNumber, pExtensionBits);
    }
  }

  @Override
  protected Integer makeBitvectorImpl(int pLength, Integer pFormula) {
    throw new UnsupportedOperationException(
        "Yices does not support making a BV formula from an INT formula as of Version 2.6.1. "
            + "Support is planned for a future release.");
  }
}
