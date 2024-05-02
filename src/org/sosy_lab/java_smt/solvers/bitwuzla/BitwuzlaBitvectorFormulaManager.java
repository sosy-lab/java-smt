// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;

public class BitwuzlaBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> {

  private final TermManager termManager;

  protected BitwuzlaBitvectorFormulaManager(
      BitwuzlaFormulaCreator pCreator,
      AbstractBooleanFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> pBmgr) {
    super(pCreator, pBmgr);
    termManager = pCreator.getTermManager();
  }

  @Override
  protected Term makeBitvectorImpl(int length, Term pParam1) {
    throw new UnsupportedOperationException("Bitwuzla does not support the theory of Integers.");
  }

  @Override
  protected Term makeBitvectorImpl(int length, BigInteger pI) {
    pI = transformValueToRange(length, pI);
    Sort sort = termManager.mk_bv_sort(length);
    return termManager.mk_bv_value(sort, pI.toString(), (short) 10);
  }

  @Override
  protected Term toIntegerFormulaImpl(Term pI, boolean signed) {
    throw new UnsupportedOperationException("Bitvector to Integers conversion is not supported.");
  }

  @Override
  protected Term negate(Term pParam1) {
    return termManager.mk_term(Kind.BV_NEG, pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_ADD, pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_SUB, pParam1, pParam2);
  }

  @Override
  protected Term divide(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return termManager.mk_term(Kind.BV_SDIV, pParam1, pParam2);
    } else {
      return termManager.mk_term(Kind.BV_UDIV, pParam1, pParam2);
    }
  }

  @Override
  protected Term remainder(Term pParam1, Term pParam2, boolean signed) {
    return termManager.mk_term(signed ? Kind.BV_SREM : Kind.BV_UREM, pParam1, pParam2);
  }

  @Override
  protected Term smodulo(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_SMOD, pParam1, pParam2);
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_MUL, pParam1, pParam2);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return termManager.mk_term(Kind.BV_SGT, pParam1, pParam2);
    } else {
      return termManager.mk_term(Kind.BV_UGT, pParam1, pParam2);
    }
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return termManager.mk_term(Kind.BV_SGE, pParam1, pParam2);
    } else {
      return termManager.mk_term(Kind.BV_UGE, pParam1, pParam2);
    }
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return termManager.mk_term(Kind.BV_SLT, pParam1, pParam2);
    } else {
      return termManager.mk_term(Kind.BV_ULT, pParam1, pParam2);
    }
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return termManager.mk_term(Kind.BV_SLE, pParam1, pParam2);
    } else {
      return termManager.mk_term(Kind.BV_ULE, pParam1, pParam2);
    }
  }

  @Override
  protected Term not(Term pParam1) {
    return termManager.mk_term(Kind.BV_NOT, pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_AND, pParam1, pParam2);
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_OR, pParam1, pParam2);
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.BV_XOR, pParam1, pParam2);
  }

  @Override
  protected Term makeVariableImpl(int pLength, String pVar) {
    Sort sort = termManager.mk_bv_sort(pLength);
    return getFormulaCreator().makeVariable(sort, pVar);
  }

  @Override
  protected Term shiftRight(Term pNumber, Term toShift, boolean signed) {
    if (signed) {
      return termManager.mk_term(Kind.BV_ASHR, pNumber, toShift);
    } else {
      return termManager.mk_term(Kind.BV_SHR, pNumber, toShift);
    }
  }

  @Override
  protected Term shiftLeft(Term pNumber, Term toShift) {
    return termManager.mk_term(Kind.BV_SHL, pNumber, toShift);
  }

  @Override
  public Term rotateLeftByConstant(Term bitVec, int toRotate) {
    return termManager.mk_term(Kind.BV_ROLI, bitVec, toRotate);
  }

  @Override
  public Term rotateLeft(Term bitVec, Term toRotate) {
    return termManager.mk_term(Kind.BV_ROL, bitVec, toRotate);
  }

  @Override
  public Term rotateRightByConstant(Term bitVec, int toRotate) {
    return termManager.mk_term(Kind.BV_RORI, bitVec, toRotate);
  }

  @Override
  public Term rotateRight(Term bitVec, Term toRotate) {
    return termManager.mk_term(Kind.BV_ROR, bitVec, toRotate);
  }

  @Override
  protected Term concat(Term number, Term pAppend) {
    return termManager.mk_term(Kind.BV_CONCAT, number, pAppend);
  }

  @Override
  protected Term extract(Term pNumber, int pMsb, int pLsb) {
    return termManager.mk_term(Kind.BV_EXTRACT, pNumber, pMsb, pLsb);
  }

  @Override
  protected Term extend(Term pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return termManager.mk_term(Kind.BV_SIGN_EXTEND, pNumber, pExtensionBits);
    } else {
      return termManager.mk_term(Kind.BV_ZERO_EXTEND, pNumber, pExtensionBits);
    }
  }
}
