// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import static com.google.common.base.Preconditions.checkArgument;

import edu.stanford.CVC4.BitVector;
import edu.stanford.CVC4.BitVectorExtract;
import edu.stanford.CVC4.BitVectorRotateLeft;
import edu.stanford.CVC4.BitVectorRotateRight;
import edu.stanford.CVC4.BitVectorSignExtend;
import edu.stanford.CVC4.BitVectorType;
import edu.stanford.CVC4.BitVectorZeroExtend;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.IntToBitVector;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

public class CVC4BitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  protected CVC4BitvectorFormulaManager(
      CVC4FormulaCreator pCreator, CVC4BooleanFormulaManager pBmgr) {
    super(pCreator, pBmgr);
    exprManager = pCreator.getEnv();
  }

  @Override
  protected Expr concat(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_CONCAT, pParam1, pParam2);
  }

  @Override
  protected Expr extract(Expr pParam1, int pMsb, int pLsb) {
    Expr ext = exprManager.mkConst(new BitVectorExtract(pMsb, pLsb));
    return exprManager.mkExpr(Kind.BITVECTOR_EXTRACT, ext, pParam1);
  }

  @Override
  protected Expr extend(Expr pParam1, int pExtensionBits, boolean signed) {
    final Expr op;
    if (signed) {
      op = exprManager.mkConst(new BitVectorSignExtend(pExtensionBits));
    } else {
      op = exprManager.mkConst(new BitVectorZeroExtend(pExtensionBits));
    }
    return exprManager.mkExpr(op, pParam1);
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, BigInteger pI) {
    pI = transformValueToRange(pLength, pI);
    return exprManager.mkConst(new BitVector(pLength, pI));
  }

  @Override
  protected Expr makeVariableImpl(int length, String varName) {
    Type type = exprManager.mkBitVectorType(length);
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Expr shiftRight(Expr pParam1, Expr pParam2, boolean signed) {
    if (signed) {
      return exprManager.mkExpr(Kind.BITVECTOR_ASHR, pParam1, pParam2);
    } else {
      return exprManager.mkExpr(Kind.BITVECTOR_LSHR, pParam1, pParam2);
    }
  }

  @Override
  protected Expr shiftLeft(Expr number, Expr toShift) {
    return exprManager.mkExpr(Kind.BITVECTOR_SHL, number, toShift);
  }

  @Override
  protected Expr rotateLeftByConstant(Expr number, int toRotate) {
    Expr op = exprManager.mkConst(new BitVectorRotateLeft(toRotate));
    return exprManager.mkExpr(op, number);
  }

  @Override
  protected Expr rotateRightByConstant(Expr number, int toRotate) {
    Expr op = exprManager.mkConst(new BitVectorRotateRight(toRotate));
    return exprManager.mkExpr(op, number);
  }

  @Override
  protected Expr not(Expr pParam1) {
    return exprManager.mkExpr(Kind.BITVECTOR_NOT, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_AND, pParam1, pParam2);
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_OR, pParam1, pParam2);
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_XOR, pParam1, pParam2);
  }

  @Override
  protected Expr negate(Expr pParam1) {
    return exprManager.mkExpr(Kind.BITVECTOR_NEG, pParam1);
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_PLUS, pParam1, pParam2);
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_SUB, pParam1, pParam2);
  }

  @Override
  protected Expr divide(Expr numerator, Expr denominator, boolean signed) {
    final Kind operator = signed ? Kind.BITVECTOR_SDIV : Kind.BITVECTOR_UDIV;
    final Expr division = exprManager.mkExpr(operator, numerator, denominator);
    // CVC4 does not align with SMTLIB standard when it comes to divide-by-zero.
    // For divide-by-zero, we compute the result as: return "1" with the opposite
    // sign than the numerator.
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(numerator)).getSize();
    final Expr zero = makeBitvectorImpl(bitsize, 0);
    final Expr one = makeBitvectorImpl(bitsize, 1);
    final Expr maxValue = makeBitvectorImpl(bitsize, -1); // all bits equal "1"
    return exprManager.mkExpr(
        Kind.ITE,
        exprManager.mkExpr(Kind.EQUAL, denominator, zero),
        exprManager.mkExpr(Kind.ITE, lessThan(numerator, zero, signed), one, maxValue),
        division);
  }

  @Override
  protected Expr remainder(Expr numerator, Expr denominator, boolean signed) {
    final Kind operator = signed ? Kind.BITVECTOR_SREM : Kind.BITVECTOR_UREM;
    final Expr remainder = exprManager.mkExpr(operator, numerator, denominator);
    // CVC4 does not align with SMTLIB standard when it comes to modulo-by-zero.
    // For modulo-by-zero, we compute the result as: "return the numerator".
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(numerator)).getSize();
    final Expr zero = makeBitvectorImpl(bitsize, 0);
    return exprManager.mkExpr(
        Kind.ITE, exprManager.mkExpr(Kind.EQUAL, denominator, zero), numerator, remainder);
  }

  @Override
  protected Expr smodulo(Expr numerator, Expr denominator) {
    final Expr modulo = exprManager.mkExpr(Kind.BITVECTOR_SMOD, numerator, denominator);
    // CVC4 does not align with SMTLIB standard when it comes to modulo-by-zero.
    // For modulo-by-zero, we compute the result as: "return the numerator".
    final int bitsize = ((BitvectorType) formulaCreator.getFormulaType(numerator)).getSize();
    final Expr zero = makeBitvectorImpl(bitsize, 0);
    return exprManager.mkExpr(
        Kind.ITE, exprManager.mkExpr(Kind.EQUAL, denominator, zero), numerator, modulo);
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.BITVECTOR_MULT, pParam1, pParam2);
  }

  @Override
  protected Expr equal(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2, boolean signed) {
    if (signed) {
      return exprManager.mkExpr(Kind.BITVECTOR_SLT, pParam1, pParam2);
    } else {
      return exprManager.mkExpr(Kind.BITVECTOR_ULT, pParam1, pParam2);
    }
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2, boolean signed) {
    if (signed) {
      return exprManager.mkExpr(Kind.BITVECTOR_SLE, pParam1, pParam2);
    } else {
      return exprManager.mkExpr(Kind.BITVECTOR_ULE, pParam1, pParam2);
    }
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2, boolean signed) {
    if (signed) {
      return exprManager.mkExpr(Kind.BITVECTOR_SGT, pParam1, pParam2);
    } else {
      return exprManager.mkExpr(Kind.BITVECTOR_UGT, pParam1, pParam2);
    }
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2, boolean signed) {
    if (signed) {
      return exprManager.mkExpr(Kind.BITVECTOR_SGE, pParam1, pParam2);
    } else {
      return exprManager.mkExpr(Kind.BITVECTOR_UGE, pParam1, pParam2);
    }
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, Expr pParam1) {
    Expr size = exprManager.mkConst(new IntToBitVector(pLength));
    return exprManager.mkExpr(Kind.INT_TO_BITVECTOR, size, pParam1);
  }

  @Override
  protected Expr toIntegerFormulaImpl(Expr pBv, boolean pSigned) {
    Expr intExpr = exprManager.mkExpr(Kind.BITVECTOR_TO_NAT, pBv);

    // CVC4 returns unsigned int by default
    if (pSigned) {

      // TODO check what is cheaper for the solver:
      // checking the first BV-bit or computing max-int-value for the given size

      final int size = Math.toIntExact(new BitVectorType(pBv.getType()).getSize());
      final BigInteger modulo = BigInteger.ONE.shiftLeft(size);
      final BigInteger maxInt = BigInteger.ONE.shiftLeft(size - 1).subtract(BigInteger.ONE);
      final Expr moduloExpr = exprManager.mkConst(new Rational(modulo.toString()));
      final Expr maxIntExpr = exprManager.mkConst(new Rational(maxInt.toString()));

      intExpr =
          exprManager.mkExpr(
              Kind.ITE,
              exprManager.mkExpr(Kind.GT, intExpr, maxIntExpr),
              exprManager.mkExpr(Kind.MINUS, intExpr, moduloExpr),
              intExpr);
    }

    return intExpr;
  }

  @Override
  protected Expr distinctImpl(List<Expr> pParam) {
    vectorExpr param = new vectorExpr();
    pParam.forEach(param::add);
    return exprManager.mkExpr(Kind.DISTINCT, param);
  }

  @Override
  protected int getBitvectorWidthImpl(Expr bitvector) {
    Type type = bitvector.getType();
    checkArgument(type.isBitVector());
    return (int) ((edu.stanford.CVC4.BitVectorType) type).getSize();
  }
}
