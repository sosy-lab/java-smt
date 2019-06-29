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
package org.sosy_lab.java_smt.solvers.boolector;

import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_add;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_and;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_concat;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_eq;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_mul;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_neg;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_not;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_or;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sdiv;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sext;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sgt;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sgte;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sll;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_slt;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_slte;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_smod;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sra;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_srl;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_sub;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_udiv;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_uext;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_ugt;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_ugte;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_ult;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_ulte;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_urem;
import static org.sosy_lab.java_smt.solvers.boolector.boolectorNativeAPI.boolector_xor;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

public class BoolectorBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Long, Long, Long, Long> {

  private final long btor;

  public BoolectorBitvectorFormulaManager(BoolectorFormulaCreator pCreator) {
    super(pCreator);
    this.btor = pCreator.getEnv();
  }

  @Override
  public Long makeBitvectorImpl(int pLength, Long pParam1) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long toIntegerFormulaImpl(Long pI, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long negate(Long bitVec) {
    return boolector_neg(btor, bitVec);
  }

  @Override
  public Long add(Long bitVec1, Long bitVec2) {
    return boolector_add(btor, bitVec1, bitVec2);
  }

  @Override
  public Long subtract(Long bitVec1, Long bitVec2) {
    return boolector_sub(btor, bitVec1, bitVec2);
  }

  @Override
  public Long divide(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_sdiv(btor, bitVec1, bitVec2);
    } else {
      return boolector_udiv(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long modulo(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_smod(btor, bitVec1, bitVec2);
    } else {
      return boolector_urem(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long multiply(Long bitVec1, Long bitVec2) {
    return boolector_mul(btor, bitVec1, bitVec2);
  }

  @Override
  public Long equal(Long bitVec1, Long bitVec2) {
    return boolector_eq(btor, bitVec1, bitVec2);
  }

  @Override
  public Long greaterThan(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_sgt(btor, bitVec1, bitVec2);
    } else {
      return boolector_ugt(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long greaterOrEquals(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_sgte(btor, bitVec1, bitVec2);
    } else {
      return boolector_ugte(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long lessThan(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_slt(btor, bitVec1, bitVec2);
    } else {
      return boolector_ult(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long lessOrEquals(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_slte(btor, bitVec1, bitVec2);
    } else {
      return boolector_ulte(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long not(Long bitVec) {
    return boolector_not(btor, bitVec);
  }

  @Override
  public Long and(Long bitVec1, Long bitVec2) {
    return boolector_and(btor, bitVec1, bitVec2);
  }

  @Override
  public Long or(Long bitVec1, Long bitVec2) {
    return boolector_or(btor, bitVec1, bitVec2);
  }

  @Override
  public Long xor(Long bitVec1, Long bitVec2) {
    return boolector_xor(btor, bitVec1, bitVec2);
  }

  @Override
  public Long makeBitvectorImpl(int pLength, BigInteger pI) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long makeVariableImpl(int pLength, String pVar) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long shiftRight(Long bitVec, Long toShift, boolean signed) {
    if(signed) {
      return boolector_sra(btor, bitVec, toShift);
    } else {
      return boolector_srl(btor, bitVec, toShift);
    }
  }

  @Override
  public Long shiftLeft(Long bitVec, Long toShift) {
    return boolector_sll(btor, bitVec, toShift);
  }

  @Override
  public Long concat(Long bitVec, Long bitVecAppend) {
    return boolector_concat(btor, bitVec, bitVecAppend);
  }

  @Override
  public Long extract(Long pNumber, int pMsb, int pLsb, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long extend(Long bitVec, int extensionBits, boolean signed) {
    if (signed) {
      return boolector_sext(btor, bitVec, extensionBits);
    } else {
      return boolector_uext(btor, bitVec, extensionBits);
    }
  }

}
