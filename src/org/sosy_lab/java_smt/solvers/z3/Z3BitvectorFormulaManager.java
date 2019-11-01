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
package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

class Z3BitvectorFormulaManager extends AbstractBitvectorFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3BitvectorFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  public Long concat(Long pFirst, Long pSecond) {
    return Native.mkConcat(z3context, pFirst, pSecond);
  }

  @Override
  public Long extract(Long pFirst, int pMsb, int pLsb, boolean pSigned) {
    return Native.mkExtract(z3context, pMsb, pLsb, pFirst);
  }

  @Override
  public Long extend(Long pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return Native.mkSignExt(z3context, pExtensionBits, pNumber);
    } else {
      return Native.mkZeroExt(z3context, pExtensionBits, pNumber);
    }
  }

  @Override
  protected Long makeBitvectorImpl(int pLength, BigInteger pI) {
    checkRange(pLength, pI);
    long sort = Native.mkBvSort(z3context, pLength);
    return Native.mkNumeral(z3context, pI.toString(), sort);
  }

  @Override
  protected Long makeBitvectorImpl(int pLength, Long pNumeralFormula) {
    return Native.mkInt2bv(z3context, pLength, pNumeralFormula);
  }

  @Override
  protected Long toIntegerFormulaImpl(Long pBVFormula, boolean pSigned) {
    return Native.mkBv2int(z3context, pBVFormula, pSigned);
  }

  @Override
  public Long makeVariableImpl(int length, String varName) {
    long type = getFormulaCreator().getBitvectorType(length);
    return getFormulaCreator().makeVariable(type, varName);
  }

  /**
   * Return a term representing the (arithmetic if signed is true) right shift of number by toShift.
   */
  @Override
  public Long shiftRight(Long number, Long toShift, boolean signed) {
    if (signed) {
      return Native.mkBvashr(z3context, number, toShift);
    } else {
      return Native.mkBvlshr(z3context, number, toShift);
    }
  }

  @Override
  public Long shiftLeft(Long number, Long toShift) {
    return Native.mkBvshl(z3context, number, toShift);
  }

  @Override
  public Long not(Long pBits) {
    return Native.mkBvnot(z3context, pBits);
  }

  @Override
  public Long and(Long pBits1, Long pBits2) {
    return Native.mkBvand(z3context, pBits1, pBits2);
  }

  @Override
  public Long or(Long pBits1, Long pBits2) {
    return Native.mkBvor(z3context, pBits1, pBits2);
  }

  @Override
  public Long xor(Long pBits1, Long pBits2) {
    return Native.mkBvxor(z3context, pBits1, pBits2);
  }

  @Override
  public Long negate(Long pNumber) {
    return Native.mkBvneg(z3context, pNumber);
  }

  @Override
  public Long add(Long pNumber1, Long pNumber2) {
    return Native.mkBvadd(z3context, pNumber1, pNumber2);
  }

  @Override
  public Long subtract(Long pNumber1, Long pNumber2) {
    return Native.mkBvsub(z3context, pNumber1, pNumber2);
  }

  @Override
  public Long divide(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return Native.mkBvsdiv(z3context, pNumber1, pNumber2);
    } else {
      return Native.mkBvudiv(z3context, pNumber1, pNumber2);
    }
  }

  @Override
  public Long modulo(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return Native.mkBvsrem(z3context, pNumber1, pNumber2);
    } else {
      return Native.mkBvurem(z3context, pNumber1, pNumber2);
    }
  }

  @Override
  public Long multiply(Long pNumber1, Long pNumber2) {
    return Native.mkBvmul(z3context, pNumber1, pNumber2);
  }

  @Override
  public Long equal(Long pNumber1, Long pNumber2) {
    return Native.mkEq(z3context, pNumber1, pNumber2);
  }

  @Override
  public Long lessThan(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return Native.mkBvslt(z3context, pNumber1, pNumber2);
    } else {
      return Native.mkBvult(z3context, pNumber1, pNumber2);
    }
  }

  @Override
  public Long lessOrEquals(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return Native.mkBvsle(z3context, pNumber1, pNumber2);
    } else {
      return Native.mkBvule(z3context, pNumber1, pNumber2);
    }
  }

  @Override
  public Long greaterThan(Long pNumber1, Long pNumber2, boolean signed) {
    return lessThan(pNumber2, pNumber1, signed);
  }

  @Override
  public Long greaterOrEquals(Long pNumber1, Long pNumber2, boolean signed) {
    return lessOrEquals(pNumber2, pNumber1, signed);
  }
}
