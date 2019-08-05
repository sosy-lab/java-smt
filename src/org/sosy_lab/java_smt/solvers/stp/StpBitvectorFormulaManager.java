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
package org.sosy_lab.java_smt.solvers.stp;

import static com.google.common.base.Preconditions.checkArgument;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

class StpBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Expr, Type, VC, Long> {

  private final VC vc;

  protected StpBitvectorFormulaManager(StpFormulaCreator pCreator) {
    super(pCreator);
    this.vc = pCreator.getEnv();
  }

  public static StpBitvectorFormulaManager create(StpFormulaCreator creator) {
    return new StpBitvectorFormulaManager(creator);
  }


  @Override
  protected Expr makeVariableImpl(int pLength, String pVar) {
    Type bvType = getFormulaCreator().getBitvectorType(pLength);
    return getFormulaCreator().makeVariable(bvType, pVar);
  }

  @Override
  public Expr makeBitvectorImpl(int pLength, long pI) {
    int i = (int) pI;
    if (i == pI && i > 0) { // fits into an int
      return StpJavaApi.vc_bv32ConstExprFromInt(vc, pI);// msat_make_bv_int_number(mathsatEnv, i,
                                                        // pLength);
    }
    return makeBitvectorImpl(pLength, BigInteger.valueOf(pI));
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, BigInteger pI) {
    if (pI.signum() < 0) {
      BigInteger max = BigInteger.valueOf(2).pow(pLength - 1);
      if (pI.compareTo(max.negate()) < 0) {
        throw new IllegalArgumentException(
            pI + " is to small for a bitvector with length " + pLength);
      }
      BigInteger n = BigInteger.valueOf(2).pow(pLength);
      pI = pI.add(n);
    }
    return StpJavaApi.vc_bvConstExprFromLL(vc, pLength, pI);
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, Expr pParam1) {
    // TODO Implement this
    // return StpJavaApi.vc_bv32ConstExprFromInt(vc, pLength);
    throw new UnsupportedOperationException(" not yet implemented yet");
  }

  @Override
  protected Expr toIntegerFormulaImpl(Expr pI, boolean pSigned) {
    // TODO IntegerFormula is not in STP
    // return null;
    throw new UnsupportedOperationException(" not yet implemented yet");
  }

  @Override
  protected Expr negate(Expr pParam1) {
    return StpJavaApi.vc_bvUMinusExpr(vc, pParam1);
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2) {
    int bitSize = confirmEqualBitSize(pParam1, pParam2);
    return StpJavaApi.vc_bvPlusExpr(vc, bitSize, pParam1, pParam2);
  }

  private int confirmEqualBitSize(Expr pParam1, Expr pParam2) {
    int bitSize = StpJavaApi.getBVInt(pParam1);
    checkArgument(bitSize == StpJavaApi.getBVInt(pParam2), "Formulae have different bit size");
    return bitSize;
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2) {
    int bitSize = confirmEqualBitSize(pParam1, pParam2);
    return StpJavaApi.vc_bvMinusExpr(vc, bitSize, pParam1, pParam2);
  }

  @Override
  protected Expr divide(Expr pParam1, Expr pParam2, boolean pSigned) {
    int bitSize = confirmEqualBitSize(pParam1, pParam2);
    return StpJavaApi.vc_bvDivExpr(vc, bitSize, pParam1, pParam2);
  }

  @Override
  protected Expr modulo(Expr pParam1, Expr pParam2, boolean pSigned) {
    int bitSize = confirmEqualBitSize(pParam1, pParam2);
    return StpJavaApi.vc_bvModExpr(vc, bitSize, pParam1, pParam2);
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2) {
    int bitSize = confirmEqualBitSize(pParam1, pParam2);
    return StpJavaApi.vc_bvModExpr(vc, bitSize, pParam1, pParam2);
  }

  @Override
  protected Expr equal(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_eqExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2, boolean pSigned) {
    return StpJavaApi.vc_bvGtExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2, boolean pSigned) {
    return StpJavaApi.vc_bvGeExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2, boolean pSigned) {
    return StpJavaApi.vc_bvLtExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2, boolean pSigned) {
    return StpJavaApi.vc_bvLeExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr not(Expr pParam1) {
    return StpJavaApi.vc_bvNotExpr(vc, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_bvAndExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_bvOrExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return StpJavaApi.vc_bvXorExpr(vc, pParam1, pParam2);
  }

  @Override
  protected Expr shiftRight(Expr pNumber, Expr pToShift, boolean pSigned) {
    int bitSize = confirmEqualBitSize(pNumber, pToShift);
    Expr retValue;
    if (pSigned) {
      retValue = StpJavaApi.vc_bvSignedRightShiftExprExpr(vc, bitSize, pNumber, pToShift);
    } else {
      retValue = StpJavaApi.vc_bvRightShiftExprExpr(vc, bitSize, pNumber, pToShift);
    }
    return retValue;
  }

  @Override
  protected Expr shiftLeft(Expr pExtract, Expr pExtract2) {
    int bitSize = confirmEqualBitSize(pExtract, pExtract);
    return StpJavaApi.vc_bvLeftShiftExprExpr(vc, bitSize, pExtract, pExtract);
  }

  @Override
  protected Expr concat(Expr pNumber, Expr pAppend) {
    return StpJavaApi.vc_bvConcatExpr(vc, pNumber, pAppend);
  }

  @Override
  protected Expr extract(Expr pNumber, int pMsb, int pLsb, boolean pSigned) {
    return StpJavaApi.vc_bvExtract(vc, pNumber, pMsb, pLsb);
  }

  @Override
  protected Expr extend(Expr pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return StpJavaApi.vc_bvSignExtend(vc, pNumber, pExtensionBits);
    } else { // TODO this should be using Unsigned Version
      return StpJavaApi.vc_bvSignExtend(vc, pNumber, pExtensionBits);
    }
  }

}