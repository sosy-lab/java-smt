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
import ap.parser.ITerm;
import ap.theories.bitvectors.ModuloArithmetic$;
import ap.types.Sort;
import ap.types.Sort$;
import com.google.common.base.Preconditions;
import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import scala.Option;

class PrincessBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  PrincessBitvectorFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected IExpression negate(IExpression pParam1) {
    return ModuloArithmetic$.MODULE$.bvneg((ITerm) pParam1);
  }

  @Override
  protected IExpression add(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvadd((ITerm) pParam1, (ITerm) pParam2);
  }

  @Override
  protected IExpression subtract(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvsub((ITerm) pParam1, (ITerm) pParam2);
  }

  @Override
  protected IExpression divide(IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvsdiv((ITerm) pParam1, (ITerm) pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvudiv((ITerm) pParam1, (ITerm) pParam2);
    }
  }

  @Override
  protected IExpression modulo(IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvsrem((ITerm) pParam1, (ITerm) pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvurem((ITerm) pParam1, (ITerm) pParam2);
    }
  }

  @Override
  protected IExpression multiply(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvmul((ITerm) pParam1, (ITerm) pParam2);
  }

  @Override
  protected IExpression equal(IExpression pParam1, IExpression pParam2) {
    return ((ITerm) pParam1).$eq$eq$eq((ITerm) pParam2);
  }

  @Override
  protected IExpression greaterThan(IExpression pParam1, IExpression pParam2, boolean signed) {
    return lessThan(pParam2, pParam1, signed);
  }

  @Override
  protected IExpression greaterOrEquals(IExpression pParam1, IExpression pParam2, boolean signed) {
    return lessOrEquals(pParam2, pParam1, signed);
  }

  @Override
  protected IExpression lessThan(IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvslt((ITerm) pParam1, (ITerm) pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvult((ITerm) pParam1, (ITerm) pParam2);
    }
  }

  @Override
  protected IExpression lessOrEquals(IExpression pParam1, IExpression pParam2, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvsle((ITerm) pParam1, (ITerm) pParam2);
    } else {
      return ModuloArithmetic$.MODULE$.bvule((ITerm) pParam1, (ITerm) pParam2);
    }
  }

  @Override
  protected IExpression not(IExpression pParam1) {
    return ModuloArithmetic$.MODULE$.bvnot((ITerm) pParam1);
  }

  @Override
  protected IExpression and(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvand((ITerm) pParam1, (ITerm) pParam2);
  }

  @Override
  protected IExpression or(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvor((ITerm) pParam1, (ITerm) pParam2);
  }

  @Override
  protected IExpression xor(IExpression pParam1, IExpression pParam2) {
    return ModuloArithmetic$.MODULE$.bvxor((ITerm) pParam1, (ITerm) pParam2);
  }

  @Override
  protected IExpression makeBitvectorImpl(int pLength, BigInteger pI) {
    pI = transformValueToRange(pLength, pI);
    return ModuloArithmetic$.MODULE$.bv(pLength, IdealInt.apply(pI));
  }

  @Override
  protected IExpression makeBitvectorImpl(int pLength, IExpression pIntegerFormula) {
    return ModuloArithmetic$.MODULE$.cast2UnsignedBV(pLength, (ITerm) pIntegerFormula);
  }

  @Override
  protected IExpression toIntegerFormulaImpl(IExpression pBVFormula, boolean signed) {
    final Sort sort = Sort$.MODULE$.sortOf((ITerm) pBVFormula);
    final Option<Object> bitWidth = PrincessFormulaCreator.getBitWidth(sort);
    Preconditions.checkArgument(bitWidth.isDefined());
    final int size = (Integer) bitWidth.get();

    // compute range for integer value,
    // example: bitWidth=4 => signed_range=[-8;7] and unsigned_range=[0;15]
    final BigInteger min;
    final BigInteger max;
    if (signed) {
      min = BigInteger.ONE.shiftLeft(size - 1).negate();
      max = BigInteger.ONE.shiftLeft(size - 1).subtract(BigInteger.ONE);
    } else {
      min = BigInteger.ZERO;
      max = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
    }

    ITerm bvInRange =
        ModuloArithmetic$.MODULE$.cast2Interval(
            IdealInt.apply(min), IdealInt.apply(max), (ITerm) pBVFormula);

    // Princess can not directly convert from BV to INT. However, adding zero helps. Ugly.
    return IExpression.i(0).$plus(bvInRange);
  }

  @Override
  protected IExpression makeVariableImpl(int pLength, String pVar) {
    Sort t = getFormulaCreator().getBitvectorType(pLength);
    return getFormulaCreator().makeVariable(t, pVar);
  }

  @Override
  protected IExpression shiftRight(IExpression pNumber, IExpression toShift, boolean signed) {
    if (signed) {
      return ModuloArithmetic$.MODULE$.bvashr((ITerm) pNumber, (ITerm) toShift);
    } else {
      return ModuloArithmetic$.MODULE$.bvlshr((ITerm) pNumber, (ITerm) toShift);
    }
  }

  @Override
  protected IExpression shiftLeft(IExpression pExtract, IExpression pExtract2) {
    return ModuloArithmetic$.MODULE$.bvshl((ITerm) pExtract, (ITerm) pExtract2);
  }

  @Override
  protected IExpression concat(IExpression number, IExpression pAppend) {
    return ModuloArithmetic$.MODULE$.concat((ITerm) number, (ITerm) pAppend);
  }

  @Override
  protected IExpression extract(IExpression pNumber, int pMsb, int pLsb, boolean pSigned) {
    // TODO: pSigned?
    return ModuloArithmetic$.MODULE$.extract(pMsb, pLsb, (ITerm) pNumber);
  }

  @Override
  protected IExpression extend(IExpression pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return ModuloArithmetic$.MODULE$.sign_extend(pExtensionBits, (ITerm) pNumber);
    } else {
      return ModuloArithmetic$.MODULE$.zero_extend(pExtensionBits, (ITerm) pNumber);
    }
  }
}
