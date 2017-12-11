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
package org.sosy_lab.java_smt.solvers.princess;

import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.ITerm;
import ap.theories.ModuloArithmetic$;
import ap.types.Sort;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import java.math.BigInteger;

class PrincessBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  PrincessBitvectorFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected IExpression negate(IExpression pParam1) {
    return ModuloArithmetic$.MODULE$.bvneg((ITerm)pParam1);
  }

  @Override
  protected IExpression add(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvadd((ITerm)pParam1, (ITerm)pParam2);
  }

  @Override
  protected IExpression subtract(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvsub((ITerm)pParam1, (ITerm)pParam2);
  }

  @Override
  protected IExpression divide(
      IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvsdiv((ITerm)pParam1, (ITerm)pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvudiv((ITerm)pParam1, (ITerm)pParam2);
    }
  }

  @Override
  protected IExpression modulo(
      IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvsmod((ITerm)pParam1, (ITerm)pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvurem((ITerm)pParam1, (ITerm)pParam2);
    }
  }

  @Override
  protected IExpression multiply(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvmul((ITerm)pParam1, (ITerm)pParam2);
  }

  @Override
  protected IExpression equal(IExpression pParam1, IExpression pParam2) {
    return ((ITerm) pParam1).$eq$eq$eq((ITerm) pParam2);
  }

  @Override
  protected IExpression greaterThan(
      IExpression pParam1, IExpression pParam2, boolean signed) {
    return lessThan(pParam2, pParam1, signed);
  }

  @Override
  protected IExpression greaterOrEquals(
      IExpression pParam1, IExpression pParam2, boolean signed) {
    return lessOrEquals(pParam2, pParam1, signed);
  }

  @Override
  protected IExpression lessThan(
      IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvslt((ITerm)pParam1, (ITerm)pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvult((ITerm)pParam1, (ITerm)pParam2);
    }
  }

  @Override
  protected IExpression lessOrEquals(
      IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvsle((ITerm)pParam1, (ITerm)pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvule((ITerm)pParam1, (ITerm)pParam2);
    }
  }

  @Override
  protected IExpression not(IExpression pParam1) {
    return ModuloArithmetic$.MODULE$.bvnot((ITerm)pParam1);
  }

  @Override
  protected IExpression and(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvand((ITerm)pParam1, (ITerm)pParam2);
  }

  @Override
  protected IExpression or(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvor((ITerm)pParam1, (ITerm)pParam2);
  }

  @Override
  protected IExpression xor(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvxor((ITerm)pParam1, (ITerm)pParam2);
  }

  @Override
  protected IExpression makeBitvectorImpl(int pLength, long pI) {
    return makeBitvectorImpl(pLength, BigInteger.valueOf(pI));
  }

  @Override
  protected IExpression makeBitvectorImpl(int pLength, BigInteger pI) {
    BigInteger n = BigInteger.valueOf(2).pow(pLength);
    if (pI.signum() < 0) {
      BigInteger max = BigInteger.valueOf(2).pow(pLength - 1);
      if (pI.compareTo(max.negate()) < 0) {
        throw new IllegalArgumentException(
            pI + " is too small for a bitvector with length " + pLength);
      }
      pI = pI.add(n);
    }
    if (pI.compareTo(n) >= 0) {
      throw new IllegalArgumentException(
          pI + " is too big for a bitvector with length " + pLength);
    }
    return ModuloArithmetic$.MODULE$.bv(pLength, IdealInt.apply(pI));
  }

  @Override
  protected IExpression makeVariableImpl(int pLength, String pVar) {
    Sort t = getFormulaCreator().getBitvectorType(pLength);
    return getFormulaCreator().makeVariable(t, pVar);
  }

  @Override
  protected IExpression shiftRight(
      IExpression pNumber, IExpression toShift, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvashr((ITerm)pNumber, (ITerm)toShift);
    } else {
      return ModuloArithmetic$.MODULE$.bvlshr((ITerm)pNumber, (ITerm)toShift);
    }
  }

  @Override
  protected IExpression shiftLeft(IExpression pExtract, IExpression pExtract2) {
    return ModuloArithmetic$.MODULE$.bvshl((ITerm)pExtract, (ITerm)pExtract2);
  }

  @Override
  protected IExpression concat(IExpression number, IExpression pAppend) {
    return ModuloArithmetic$.MODULE$.concat((ITerm)number, (ITerm)pAppend);
  }

  @Override
  protected IExpression extract(
      IExpression pNumber, int pMsb, int pLsb, boolean pSigned) {
    // TODO: pSigned?
    return ModuloArithmetic$.MODULE$.extract(pMsb, pLsb, (ITerm)pNumber);
  }

  @Override
  protected IExpression extend(IExpression pNumber, int pExtensionBits,
                               boolean pSigned) {
    if (pSigned) {
      return ModuloArithmetic$.MODULE$.sign_extend(pExtensionBits, (ITerm)pNumber);
    } else {
      return ModuloArithmetic$.MODULE$.zero_extend(pExtensionBits, (ITerm)pNumber);
    }
  }

}
