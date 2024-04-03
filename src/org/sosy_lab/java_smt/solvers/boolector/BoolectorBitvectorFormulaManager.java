// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_add;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_and;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_concat;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_eq;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_mul;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_neg;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_not;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_or;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_rol;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_roli;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_ror;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_rori;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sdiv;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sext;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sgt;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sgte;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sll;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_slt;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_slte;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_smod;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sra;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_srem;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_srl;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_sub;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_udiv;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_uext;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_ugt;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_ugte;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_ult;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_ulte;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_urem;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_xor;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

class BoolectorBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Long, Long, Long, Long> {

  private final long btor;

  BoolectorBitvectorFormulaManager(
      BoolectorFormulaCreator creator, BoolectorBooleanFormulaManager pBmgr) {
    super(creator, pBmgr);
    this.btor = creator.getEnv();
  }

  @Override
  public Long makeBitvectorImpl(int pLength, BigInteger pI) {
    pI = transformValueToRange(pLength, pI);
    long sort = BtorJNI.boolector_bitvec_sort(btor, pLength);
    return BtorJNI.boolector_constd(btor, sort, pI.toString());
  }

  @Override
  protected Long makeBitvectorImpl(int length, Long value) {
    // The value is a pointer to an expression. Do not use the plain numeral value.
    throw new UnsupportedOperationException("Boolector does not support INT theory");
  }

  @Override
  public Long toIntegerFormulaImpl(Long pI, boolean pSigned) {
    throw new UnsupportedOperationException("BV to INT conversion is not supported.");
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
  public Long remainder(Long bitVec1, Long bitVec2, boolean signed) {
    if (signed) {
      return boolector_srem(btor, bitVec1, bitVec2);
    } else {
      return boolector_urem(btor, bitVec1, bitVec2);
    }
  }

  @Override
  public Long smodulo(Long bitVec1, Long bitVec2) {
    return boolector_smod(btor, bitVec1, bitVec2);
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
  public Long makeVariableImpl(int pLength, String pVar) {
    long sort = BtorJNI.boolector_bitvec_sort(btor, pLength);
    return getFormulaCreator().makeVariable(sort, pVar);
  }

  @Override
  public Long shiftRight(Long bitVec, Long toShift, boolean signed) {
    if (signed) {
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
  public Long rotateLeftByConstant(Long bitVec, int toRotate) {
    return boolector_roli(btor, bitVec, toRotate);
  }

  @Override
  public Long rotateLeft(Long bitVec, Long toRotate) {
    return boolector_rol(btor, bitVec, toRotate);
  }

  @Override
  public Long rotateRightByConstant(Long bitVec, int toRotate) {
    return boolector_rori(btor, bitVec, toRotate);
  }

  @Override
  public Long rotateRight(Long bitVec, Long toRotate) {
    return boolector_ror(btor, bitVec, toRotate);
  }

  @Override
  public Long concat(Long bitVec, Long bitVecAppend) {
    return boolector_concat(btor, bitVec, bitVecAppend);
  }

  @Override
  public Long extract(Long pNode, int pMsb, int pLsb) {
    return BtorJNI.boolector_slice(btor, pNode, pMsb, pLsb);
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
