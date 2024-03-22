// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Op;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

public class CVC5BitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  protected CVC5BitvectorFormulaManager(
      CVC5FormulaCreator pCreator, CVC5BooleanFormulaManager pBmgr) {
    super(pCreator, pBmgr);
    solver = pCreator.getEnv();
  }

  @Override
  protected Term concat(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_CONCAT, pParam1, pParam2);
  }

  @Override
  protected Term extract(Term pParam1, int pMsb, int pLsb) {
    Op ext;
    try {
      if (pMsb < pLsb || pMsb >= pParam1.getSort().getBitVectorSize() || pLsb < 0 || pMsb < 0) {
        ext = solver.mkOp(Kind.BITVECTOR_EXTRACT, 0, 0);
      } else {
        ext = solver.mkOp(Kind.BITVECTOR_EXTRACT, pMsb, pLsb);
      }
      return solver.mkTerm(ext, pParam1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector extract from bit "
              + pMsb
              + " to bit "
              + pLsb
              + " in term "
              + pParam1
              + ".",
          e);
    }
  }

  @Override
  protected Term extend(Term pParam1, int pExtensionBits, boolean signed) {
    final Op op;
    try {
      if (signed) {
        op = solver.mkOp(Kind.BITVECTOR_SIGN_EXTEND, pExtensionBits);
      } else {
        op = solver.mkOp(Kind.BITVECTOR_ZERO_EXTEND, pExtensionBits);
      }
      return solver.mkTerm(op, pParam1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector extend with term "
              + pParam1
              + " and t "
              + pExtensionBits
              + " extension bits.",
          e);
    }
  }

  @Override
  protected Term makeBitvectorImpl(int pLength, BigInteger pI) {
    pI = transformValueToRange(pLength, pI);
    try {
      // Use String conversion as it can hold more values
      return solver.mkBitVector(pLength, pI.toString(), 10);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector with length "
              + pLength
              + " and value "
              + pI
              + ".",
          e);
    }
  }

  @Override
  protected Term makeVariableImpl(int length, String varName) {
    try {
      Sort type = solver.mkBitVectorSort(length);
      return getFormulaCreator().makeVariable(type, varName);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector variable with length "
              + length
              + " and name "
              + varName
              + ".",
          e);
    }
  }

  @Override
  protected Term shiftRight(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_ASHR, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_LSHR, pParam1, pParam2);
    }
  }

  @Override
  protected Term shiftLeft(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_SHL, pParam1, pParam2);
  }

  @Override
  protected Term rotateLeftByConstant(Term pNumber, int pToRotate) {
    try {
      Op op = solver.mkOp(Kind.BITVECTOR_ROTATE_LEFT, pToRotate);
      return solver.mkTerm(op, pNumber);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          String.format("You tried rotation a bitvector %s with shift %d", pNumber, pToRotate), e);
    }
  }

  @Override
  protected Term rotateRightByConstant(Term pNumber, int pToRotate) {
    try {
      Op op = solver.mkOp(Kind.BITVECTOR_ROTATE_RIGHT, pToRotate);
      return solver.mkTerm(op, pNumber);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          String.format("You tried rotation a bitvector %s with shift %d", pNumber, pToRotate), e);
    }
  protected Term rotateRight(Term pNumber, Term toRotate) {
    // cvc5 does not support non-literal rotation, so we rewrite it to (bvor (bvlshr pNumber
    // toRotate) (bvshl pNumber (bvsub size toRotate)))
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(pNumber)).getSize();
    final Term size = this.makeBitvectorImpl(bitsize, bitsize);
    return or(shiftRight(pNumber, toRotate, false), shiftLeft(pNumber, subtract(size, toRotate)));
  }

  @Override
  protected Term rotateLeft(Term pNumber, Term toRotate) {
    // cvc5 does not support non-literal rotation, so we rewrite it to (bvor (bvshl pNumber
    // toRotate) (bvlshr pNumber (bvsub size toRotate)))
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(pNumber)).getSize();
    final Term size = this.makeBitvectorImpl(bitsize, bitsize);
    return or(shiftLeft(pNumber, toRotate), shiftRight(pNumber, subtract(size, toRotate), false));
  }

  @Override
  protected Term not(Term pParam1) {
    return solver.mkTerm(Kind.BITVECTOR_NOT, pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_AND, pParam1, pParam2);
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_OR, pParam1, pParam2);
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_XOR, pParam1, pParam2);
  }

  @Override
  protected Term negate(Term pParam1) {
    return solver.mkTerm(Kind.BITVECTOR_NEG, pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_ADD, pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_SUB, pParam1, pParam2);
  }

  @Override
  protected Term divide(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_SDIV, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_UDIV, pParam1, pParam2);
    }
  }

  @Override
  protected Term modulo(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_SREM, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_UREM, pParam1, pParam2);
    }
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.BITVECTOR_MULT, pParam1, pParam2);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_SLT, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_ULT, pParam1, pParam2);
    }
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_SLE, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_ULE, pParam1, pParam2);
    }
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_SGT, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_UGT, pParam1, pParam2);
    }
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2, boolean signed) {
    if (signed) {
      return solver.mkTerm(Kind.BITVECTOR_SGE, pParam1, pParam2);
    } else {
      return solver.mkTerm(Kind.BITVECTOR_UGE, pParam1, pParam2);
    }
  }

  @Override
  protected Term makeBitvectorImpl(int pLength, Term pParam1) {
    try {
      Op length = solver.mkOp(Kind.INT_TO_BITVECTOR, pLength);
      return solver.mkTerm(length, pParam1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector out of a integer term "
              + pParam1
              + " with length "
              + pLength
              + ".",
          e);
    }
  }

  @Override
  protected Term toIntegerFormulaImpl(Term pBv, boolean pSigned) {
    Term intExpr = solver.mkTerm(Kind.BITVECTOR_TO_NAT, pBv);

    // CVC5 returns unsigned int by default
    if (pSigned && pBv.getSort().isBitVector()) {

      // TODO check what is cheaper for the solver:
      // checking the first BV-bit or computing max-int-value for the given size

      final int size = Math.toIntExact(pBv.getSort().getBitVectorSize());
      final BigInteger modulo = BigInteger.ONE.shiftLeft(size);
      final BigInteger maxInt = BigInteger.ONE.shiftLeft(size - 1).subtract(BigInteger.ONE);
      final Term moduloExpr = solver.mkInteger(modulo.longValue());
      final Term maxIntExpr = solver.mkInteger(maxInt.longValue());

      intExpr =
          solver.mkTerm(
              Kind.ITE,
              solver.mkTerm(Kind.GT, intExpr, maxIntExpr),
              solver.mkTerm(Kind.SUB, intExpr, moduloExpr),
              intExpr);
    }

    return intExpr;
  }

  @Override
  protected Term distinctImpl(List<Term> pParam) {
    return solver.mkTerm(Kind.DISTINCT, pParam.toArray(new Term[0]));
  }
}
