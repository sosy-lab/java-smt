/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.z3java;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import org.sosy_lab.solver.basicimpl.AbstractBitvectorFormulaManager;

import java.math.BigInteger;

class Z3BitvectorFormulaManager extends AbstractBitvectorFormulaManager<Expr, Sort, Context> {

  private final Context z3context;

  Z3BitvectorFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  static BitVecExpr toBV(Expr e) {
    return (BitVecExpr)e;
  }

  @Override
  public Expr concat(Expr pFirst, Expr pSecond) {
    return z3context.mkConcat(toBV(pFirst), toBV(pSecond));
  }

  @Override
  public Expr extract(Expr pFirst, int pMsb, int pLsb, boolean pSigned) {
    return z3context.mkExtract(pMsb, pLsb, toBV(pFirst));
  }

  @Override
  public Expr extend(Expr pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return z3context.mkSignExt(pExtensionBits, toBV(pNumber));
    } else {
      return z3context.mkZeroExt(pExtensionBits, toBV(pNumber));
    }
  }

  @Override
  public Expr makeBitvectorImpl(int pLength, long pI) {
    return z3context.mkBV(pI, pLength);
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, BigInteger pI) {
    return z3context.mkBV(pI.toString(), pLength);
  }

  @Override
  public Expr makeVariableImpl(int length, String varName) {
    Sort type = getFormulaCreator().getBitvectorType(length);
    return getFormulaCreator().makeVariable(type, varName);
  }

  /**
   * Return a term representing the (arithmetic if signed is true) right shift of number by toShift.
   */
  @Override
  public Expr shiftRight(Expr number, Expr toShift, boolean signed) {
    if (signed) {
      return z3context.mkBVASHR(toBV(number), toBV(toShift));
    } else {
      return z3context.mkBVLSHR(toBV(number), toBV(toShift));
    }
  }

  @Override
  public Expr shiftLeft(Expr number, Expr toShift) {
    return z3context.mkBVSHL(toBV(number), toBV(toShift));
  }

  @Override
  public Expr not(Expr pBits) {
    return z3context.mkBVNot(toBV(pBits));
  }

  @Override
  public Expr and(Expr pBits1, Expr pBits2) {
    return z3context.mkBVAND(toBV(pBits1), toBV(pBits2));
  }

  @Override
  public Expr or(Expr pBits1, Expr pBits2) {
    return z3context.mkBVOR(toBV(pBits1), toBV(pBits2));
  }

  @Override
  public Expr xor(Expr pBits1, Expr pBits2) {
    return z3context.mkBVXOR(toBV(pBits1), toBV(pBits2));
  }

  @Override
  public Expr negate(Expr pNumber) {
    return z3context.mkBVNeg(toBV(pNumber));
  }

  @Override
  public Expr add(Expr pNumber1, Expr pNumber2) {
    return z3context.mkBVAdd(toBV(pNumber1), toBV(pNumber2));
  }

  @Override
  public Expr subtract(Expr pNumber1, Expr pNumber2) {
    return z3context.mkBVSub(toBV(pNumber1), toBV(pNumber2));
  }

  @Override
  public Expr divide(Expr pNumber1, Expr pNumber2, boolean signed) {
    if (signed) {
      return z3context.mkBVSDiv(toBV(pNumber1), toBV(pNumber2));
    } else {
      return z3context.mkBVUDiv(toBV(pNumber1), toBV(pNumber2));
    }
  }

  @Override
  public Expr modulo(Expr pNumber1, Expr pNumber2, boolean signed) {
    if (signed) {
      return z3context.mkBVSRem(toBV(pNumber1), toBV(pNumber2));
    } else {
      return z3context.mkBVURem(toBV(pNumber1), toBV(pNumber2));
    }
  }

  @Override
  protected Expr modularCongruence(Expr pNumber1, Expr pNumber2, long pModulo) {
    return z3context.mkTrue();
  }

  @Override
  public Expr multiply(Expr pNumber1, Expr pNumber2) {
    return z3context.mkBVMul(toBV(pNumber1), toBV(pNumber2));
  }

  @Override
  public Expr equal(Expr pNumber1, Expr pNumber2) {
    return z3context.mkEq(toBV(pNumber1), toBV(pNumber2));
  }

  @Override
  public Expr lessThan(Expr pNumber1, Expr pNumber2, boolean signed) {
    if (signed) {
      return z3context.mkBVSLT(toBV(pNumber1), toBV(pNumber2));
    } else {
      return z3context.mkBVULT(toBV(pNumber1), toBV(pNumber2));
    }
  }

  @Override
  public Expr lessOrEquals(Expr pNumber1, Expr pNumber2, boolean signed) {
    if (signed) {
      return z3context.mkBVSLE(toBV(pNumber1), toBV(pNumber2));
    } else {
      return z3context.mkBVULE(toBV(pNumber1), toBV(pNumber2));
    }
  }

  @Override
  public Expr greaterThan(Expr pNumber1, Expr pNumber2, boolean signed) {
    return lessThan(pNumber2, pNumber1, signed);
  }

  @Override
  public Expr greaterOrEquals(Expr pNumber1, Expr pNumber2, boolean signed) {
    return lessOrEquals(pNumber2, pNumber1, signed);
  }
}
