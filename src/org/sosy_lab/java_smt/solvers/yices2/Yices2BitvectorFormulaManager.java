/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvadd;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvand2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvashr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconcat2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_int32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_int64;
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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sign_extend;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_zero_extend;

import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

public class Yices2BitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2BitvectorFormulaManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
  }

  @Override
  protected Integer makeBitvectorImpl(int pLength, long pParam1) {
    // TODO Check size constraints/ Unsure if correct
    if (Long.signum(pParam1) < 0) {
      long max = (long) Math.pow(2, (pLength - 1));
      if (Math.abs(pParam1) > max) {
        throw new IllegalArgumentException(
            pParam1 + " can not be represented as a signed bv of length " + pLength);
      }
    } else {
      long max = (long) Math.pow(2, pLength);
      if (pParam1 >= max) {
        throw new IllegalArgumentException(
            pParam1 + " can not be represented as a signed bv of length " + pLength);
      }
    }
    int i = (int) pParam1;
    if (i == pParam1) {
      return yices_bvconst_int32(pLength, i);
    } else {
      return yices_bvconst_int64(pLength, pParam1);
    }
  }

  @Override
  protected Integer toIntegerFormulaImpl(Integer bvFormula, boolean pSigned) {
    // TODO Check if actually true
    throw new UnsupportedOperationException(
        "Yices dows not support making an INT formula from a BV formula.");
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
  protected Integer makeBitvectorImpl(int pLength, BigInteger pI) {
    if (pI.signum() < 0) {
      BigInteger max = BigInteger.valueOf(2).pow(pLength - 1);
      if (pI.compareTo(max.negate()) < 0) {
        throw new IllegalArgumentException(
            pI + " is to small for a bitvector with length " + pLength);
      }
      BigInteger n = BigInteger.valueOf(2).pow(pLength);
      pI = pI.add(n);
    }
    String bits = pI.toString(2);
    if (bits.length() > pLength) {
      bits = bits.substring(bits.length() - pLength, bits.length());
    } else if (bits.length() < pLength) {
      bits = Strings.padStart(bits, pLength, '0');
    }
    // TODO check size of bits against pLength
    Preconditions.checkArgument(bits.length() == pLength, "Bitvector has unexpected size.");
    return yices_parse_bvbin(bits);
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
  protected Integer concat(Integer pNumber, Integer pAppend) {
    return yices_bvconcat2(pNumber, pAppend);
  }

  @Override
  protected Integer extract(Integer pNumber, int pMsb, int pLsb, boolean pSigned) {
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
    // TODO Check if actually true
    throw new UnsupportedOperationException(
        "Yices does not support making a BV formula from an INT formula.");
  }
}
