// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

final class LeanSmtBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Long, LeanSmtType, Long, LeanSmtFunctionDecl> {

  LeanSmtBitvectorFormulaManager(
      LeanSmtFormulaCreator pCreator, LeanSmtBooleanFormulaManager pBooleanFormulaManager) {
    super(pCreator, pBooleanFormulaManager);
  }

  private LeanSmtFormulaCreator creator() {
    return (LeanSmtFormulaCreator) getFormulaCreator();
  }

  private static String indexedSymbol(String op, int index) {
    return "(_ " + op + " " + index + ")";
  }

  private static String extractSymbol(int msb, int lsb) {
    return "(_ extract " + msb + " " + lsb + ")";
  }

  private int bitvectorSize(long term) {
    FormulaType<?> type = creator().getFormulaType(term);
    return ((FormulaType.BitvectorType) type).getSize();
  }

  private long mkBvUnary(String symbol, FunctionDeclarationKind kind, long arg) {
    return creator().makeUnary(symbol, kind, creator().getFormulaType(arg), arg);
  }

  private long mkBvBinary(
      String symbol, FunctionDeclarationKind kind, long arg1, long arg2) {
    return creator().makeBinary(symbol, kind, creator().getFormulaType(arg1), arg1, arg2);
  }

  private long mkBvCompare(
      String symbol, FunctionDeclarationKind kind, long arg1, long arg2) {
    return creator().makeBinary(symbol, kind, FormulaType.BooleanType, arg1, arg2);
  }

  @Override
  protected Long makeBitvectorImpl(int pLength, BigInteger pI) {
    BigInteger value = transformValueToRange(pLength, pI);
    return creator().makeBitvectorConstant(pLength, value);
  }

  @Override
  protected Long makeBitvectorImpl(int pLength, Long pParam1) {
    return creator().makeIntToBitvectorTerm(pLength, pParam1);
  }

  @Override
  protected Long toIntegerFormulaImpl(Long pBv, boolean signed) {
    LeanSmtFormulaCreator creator = creator();
    Object value = creator.convertValue(pBv);
    if (value instanceof BigInteger) {
      BigInteger unsignedValue = (BigInteger) value;
      if (!signed) {
        return creator.makeIntConstant(unsignedValue);
      }
      int size = bitvectorSize(pBv);
      BigInteger modulus = BigInteger.ONE.shiftLeft(size);
      BigInteger signedValue =
          unsignedValue.testBit(size - 1) ? unsignedValue.subtract(modulus) : unsignedValue;
      return creator.makeIntConstant(signedValue);
    }
    long unsigned =
        creator.makeUnary(
            "ubv_to_int", FunctionDeclarationKind.UBV_TO_INT, FormulaType.IntegerType, pBv);
    if (!signed) {
      return unsigned;
    }
    return creator.makeSignedBitvectorToIntegerTerm(pBv);
  }

  @Override
  protected Long concat(Long pParam1, Long pParam2) {
    int resultSize = bitvectorSize(pParam1) + bitvectorSize(pParam2);
    return creator()
        .makeBinary(
            "concat",
            FunctionDeclarationKind.BV_CONCAT,
            FormulaType.getBitvectorTypeWithSize(resultSize),
            pParam1,
            pParam2);
  }

  @Override
  protected Long extract(Long pParam1, int pMsb, int pLsb) {
    int resultSize = pMsb - pLsb + 1;
    return creator()
        .makeUnary(
            extractSymbol(pMsb, pLsb),
            FunctionDeclarationKind.BV_EXTRACT,
            FormulaType.getBitvectorTypeWithSize(resultSize),
            pParam1);
  }

  @Override
  protected Long extend(Long pParam1, int pExtensionBits, boolean signed) {
    int resultSize = bitvectorSize(pParam1) + pExtensionBits;
    String op = signed ? "sign_extend" : "zero_extend";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SIGN_EXTENSION : FunctionDeclarationKind.BV_ZERO_EXTENSION;
    return creator()
        .makeUnary(
            indexedSymbol(op, pExtensionBits),
            kind,
            FormulaType.getBitvectorTypeWithSize(resultSize),
            pParam1);
  }

  @Override
  protected Long shiftRight(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvashr" : "bvlshr";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_ASHR : FunctionDeclarationKind.BV_LSHR;
    return mkBvBinary(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long shiftLeft(Long pParam1, Long pParam2) {
    return mkBvBinary("bvshl", FunctionDeclarationKind.BV_SHL, pParam1, pParam2);
  }

  @Override
  protected Long rotateLeftByConstant(Long pNumber, int pToRotate) {
    return creator()
        .makeUnary(
            indexedSymbol("rotate_left", pToRotate),
            FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT,
            creator().getFormulaType(pNumber),
            pNumber);
  }

  @Override
  protected Long rotateRightByConstant(Long pNumber, int pToRotate) {
    return creator()
        .makeUnary(
            indexedSymbol("rotate_right", pToRotate),
            FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT,
            creator().getFormulaType(pNumber),
            pNumber);
  }

  @Override
  protected Long not(Long pParam1) {
    return mkBvUnary("bvnot", FunctionDeclarationKind.BV_NOT, pParam1);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    return mkBvBinary("bvand", FunctionDeclarationKind.BV_AND, pParam1, pParam2);
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    return mkBvBinary("bvor", FunctionDeclarationKind.BV_OR, pParam1, pParam2);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return mkBvBinary("bvxor", FunctionDeclarationKind.BV_XOR, pParam1, pParam2);
  }

  @Override
  protected Long negate(Long pParam1) {
    return mkBvUnary("bvneg", FunctionDeclarationKind.BV_NEG, pParam1);
  }

  @Override
  protected Long add(Long pParam1, Long pParam2) {
    return mkBvBinary("bvadd", FunctionDeclarationKind.BV_ADD, pParam1, pParam2);
  }

  @Override
  protected Long subtract(Long pParam1, Long pParam2) {
    return mkBvBinary("bvsub", FunctionDeclarationKind.BV_SUB, pParam1, pParam2);
  }

  @Override
  protected Long divide(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvsdiv" : "bvudiv";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SDIV : FunctionDeclarationKind.BV_UDIV;
    return mkBvBinary(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long remainder(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvsrem" : "bvurem";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SREM : FunctionDeclarationKind.BV_UREM;
    return mkBvBinary(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long smodulo(Long pParam1, Long pParam2) {
    return mkBvBinary("bvsmod", FunctionDeclarationKind.BV_SMOD, pParam1, pParam2);
  }

  @Override
  protected Long multiply(Long pParam1, Long pParam2) {
    return mkBvBinary("bvmul", FunctionDeclarationKind.BV_MUL, pParam1, pParam2);
  }

  @Override
  protected Long equal(Long pParam1, Long pParam2) {
    return mkBvCompare("=", FunctionDeclarationKind.BV_EQ, pParam1, pParam2);
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvslt" : "bvult";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SLT : FunctionDeclarationKind.BV_ULT;
    return mkBvCompare(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvsle" : "bvule";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SLE : FunctionDeclarationKind.BV_ULE;
    return mkBvCompare(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvsgt" : "bvugt";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SGT : FunctionDeclarationKind.BV_UGT;
    return mkBvCompare(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2, boolean signed) {
    String op = signed ? "bvsge" : "bvuge";
    FunctionDeclarationKind kind =
        signed ? FunctionDeclarationKind.BV_SGE : FunctionDeclarationKind.BV_UGE;
    return mkBvCompare(op, kind, pParam1, pParam2);
  }

  @Override
  protected Long makeVariableImpl(int pLength, String pVarName) {
    return creator().makeVariable(LeanSmtType.bitvector(pLength), pVarName);
  }
}
