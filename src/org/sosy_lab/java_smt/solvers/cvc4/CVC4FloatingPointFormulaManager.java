// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.collect.ImmutableList;
import edu.stanford.CVC4.BitVector;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.FloatingPoint;
import edu.stanford.CVC4.FloatingPointConvertSort;
import edu.stanford.CVC4.FloatingPointSize;
import edu.stanford.CVC4.FloatingPointToFPFloatingPoint;
import edu.stanford.CVC4.FloatingPointToFPIEEEBitVector;
import edu.stanford.CVC4.FloatingPointToFPSignedBitVector;
import edu.stanford.CVC4.FloatingPointToFPUnsignedBitVector;
import edu.stanford.CVC4.FloatingPointToSBV;
import edu.stanford.CVC4.FloatingPointToUBV;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.RoundingMode;
import edu.stanford.CVC4.Type;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

public class CVC4FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;
  private final Expr roundingMode;

  protected CVC4FloatingPointFormulaManager(
      CVC4FormulaCreator pCreator, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(pCreator);
    exprManager = pCreator.getEnv();
    roundingMode = getRoundingModeImpl(pFloatingPointRoundingMode);
  }

  // TODO Is there a difference in `FloatingPointSize` and `FloatingPointType` in CVC4?
  // They are both just pairs of `exponent size` and `significant size`.

  private static FloatingPointSize getFPSize(FloatingPointType pType) {
    long pExponentSize = pType.getExponentSize();
    long pMantissaSize = pType.getMantissaSize();
    return new FloatingPointSize(pExponentSize, pMantissaSize + 1); // plus sign bit
  }

  @Override
  protected Expr getDefaultRoundingMode() {
    return roundingMode;
  }

  @Override
  protected Expr getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    switch (pFloatingPointRoundingMode) {
      case NEAREST_TIES_TO_EVEN:
        return exprManager.mkConst(RoundingMode.roundNearestTiesToEven);
      case NEAREST_TIES_AWAY:
        return exprManager.mkConst(RoundingMode.roundNearestTiesToAway);
      case TOWARD_POSITIVE:
        return exprManager.mkConst(RoundingMode.roundTowardPositive);
      case TOWARD_NEGATIVE:
        return exprManager.mkConst(RoundingMode.roundTowardNegative);
      case TOWARD_ZERO:
        return exprManager.mkConst(RoundingMode.roundTowardZero);
      default:
        throw new AssertionError("Unexpected branch");
    }
  }

  @Override
  protected Expr makeNumberImpl(double pN, FloatingPointType pType, Expr pRoundingMode) {
    return makeNumberImpl(Double.toString(pN), pType, pRoundingMode);
  }

  @Override
  protected Expr makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    final String signStr = sign.isNegative() ? "1" : "0";
    final String exponentStr = getBvRepresentation(exponent, type.getExponentSize());
    final String mantissaStr = getBvRepresentation(mantissa, type.getMantissaSize());
    final String bitvecStr = signStr + exponentStr + mantissaStr;
    final BitVector bitVector = new BitVector(bitvecStr, 2);
    final FloatingPoint fp =
        new FloatingPoint(type.getExponentSize(), type.getMantissaSize() + 1, bitVector);
    return exprManager.mkConst(fp);
  }

  @Override
  protected Expr makeNumberAndRound(String pN, FloatingPointType pType, Expr pRoundingMode) {
    try {
      if (isNegativeZero(Double.valueOf(pN))) {
        return exprManager.mkConst(FloatingPoint.makeZero(getFPSize(pType), /* sign */ true));
      }
    } catch (NumberFormatException e) {
      // ignore and fallback to floating point from rational numbers
    }

    final Rational rat = toRational(pN);
    final BigInteger upperBound =
        getBiggestNumberBeforeInf(pType.getMantissaSize(), pType.getExponentSize());

    if (rat.greater(Rational.fromDecimal(upperBound.negate().toString()))
        && rat.less(Rational.fromDecimal(upperBound.toString()))) {
      return exprManager.mkConst(
          new FloatingPoint(getFPSize(pType), pRoundingMode.getConstRoundingMode(), rat));

    } else { // out of range
      if (rat.greater(Rational.fromDecimal("0"))) {
        return makePlusInfinityImpl(pType);
      } else {
        return makeMinusInfinityImpl(pType);
      }
    }
  }

  // TODO lookup why this number works: <code>2**(2**(exp-1)) - 2**(2**(exp-1)-2-mant)</code>
  private static BigInteger getBiggestNumberBeforeInf(int mantissa, int exponent) {
    int boundExponent = BigInteger.valueOf(2).pow(exponent - 1).intValueExact();
    BigInteger upperBoundExponent = BigInteger.valueOf(2).pow(boundExponent);
    int mantissaExponent = BigInteger.valueOf(2).pow(exponent - 1).intValueExact() - 2 - mantissa;
    if (mantissaExponent >= 0) { // ignore negative mantissaExponent
      upperBoundExponent = upperBoundExponent.subtract(BigInteger.valueOf(2).pow(mantissaExponent));
    }
    return upperBoundExponent;
  }

  /**
   * Try to convert a String numeral into a Rational.
   *
   * <p>If we do not check all invalid formatted numbers in our own code, CVC4 will fail hard and
   * immediately terminate the whole program.
   */
  private Rational toRational(String pN) throws NumberFormatException {
    try {
      // first try something like -123.567
      return Rational.fromDecimal(new BigDecimal(pN).toPlainString());

    } catch (NumberFormatException e1) {
      try {
        // then try something like -123/456

        @SuppressWarnings("unused") // check format before calling CVC4
        org.sosy_lab.common.rationals.Rational unused =
            org.sosy_lab.common.rationals.Rational.ofString(pN);

        return new Rational(pN);

      } catch (NumberFormatException e2) {
        // we cannot handle the number
        throw new NumberFormatException("invalid numeral: " + pN);
      }
    }
  }

  @Override
  protected Expr makeVariableImpl(String varName, FloatingPointType pType) {
    return formulaCreator.makeVariable(formulaCreator.getFloatingPointType(pType), varName);
  }

  @Override
  protected Expr makePlusInfinityImpl(FloatingPointType pType) {
    return exprManager.mkConst(FloatingPoint.makeInf(getFPSize(pType), /* sign */ false));
  }

  @Override
  protected Expr makeMinusInfinityImpl(FloatingPointType pType) {
    return exprManager.mkConst(FloatingPoint.makeInf(getFPSize(pType), /* sign */ true));
  }

  @Override
  protected Expr makeNaNImpl(FloatingPointType pType) {
    return exprManager.mkConst(FloatingPoint.makeNaN(getFPSize(pType)));
  }

  @Override
  protected Expr castToImpl(
      Expr pNumber, boolean pSigned, FormulaType<?> pTargetType, Expr pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      FloatingPointConvertSort fpConvertSort = new FloatingPointConvertSort(getFPSize(targetType));
      Expr op = exprManager.mkConst(new FloatingPointToFPFloatingPoint(fpConvertSort));
      return exprManager.mkExpr(op, pRoundingMode, pNumber);

    } else if (pTargetType.isBitvectorType()) {
      BitvectorType targetType = (BitvectorType) pTargetType;
      Expr op =
          pSigned
              ? exprManager.mkConst(new FloatingPointToSBV(targetType.getSize()))
              : exprManager.mkConst(new FloatingPointToUBV(targetType.getSize()));
      return exprManager.mkExpr(op, pRoundingMode, pNumber);

    } else if (pTargetType.isRationalType()) {
      return exprManager.mkExpr(Kind.FLOATINGPOINT_TO_REAL, pNumber);

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  @Override
  protected Expr castFromImpl(
      Expr pNumber, boolean pSigned, FloatingPointType pTargetType, Expr pRoundingMode) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);
    if (formulaType.isFloatingPointType()) {
      return castToImpl(pNumber, pSigned, pTargetType, pRoundingMode);

    } else if (formulaType.isBitvectorType()) {
      long pExponentSize = pTargetType.getExponentSize();
      long pMantissaSize = pTargetType.getMantissaSize();
      FloatingPointSize fpSize = new FloatingPointSize(pExponentSize, pMantissaSize + 1);
      FloatingPointConvertSort fpConvert = new FloatingPointConvertSort(fpSize);
      final Expr op;
      if (pSigned) {
        op = exprManager.mkConst(new FloatingPointToFPSignedBitVector(fpConvert));
      } else {
        op = exprManager.mkConst(new FloatingPointToFPUnsignedBitVector(fpConvert));
      }
      return exprManager.mkExpr(op, pRoundingMode, pNumber);

    } else {
      return genericCast(pNumber, pTargetType);
    }
  }

  private Expr genericCast(Expr pNumber, FormulaType<?> pTargetType) {
    Type type = pNumber.getType();
    FormulaType<?> argType = getFormulaCreator().getFormulaType(pNumber);
    Expr castFuncDecl =
        getFormulaCreator()
            .declareUFImpl(
                "__cast_" + argType + "_to_" + pTargetType,
                toSolverType(pTargetType),
                ImmutableList.of(type));
    return exprManager.mkExpr(Kind.APPLY_UF, castFuncDecl, pNumber);
  }

  @Override
  protected Expr negate(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_NEG, pParam1);
  }

  @Override
  protected Expr abs(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ABS, pParam1);
  }

  @Override
  protected Expr max(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_MAX, pParam1, pParam2);
  }

  @Override
  protected Expr min(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_MIN, pParam1, pParam2);
  }

  @Override
  protected Expr sqrt(Expr pParam1, Expr pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_SQRT, pRoundingMode, pParam1);
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2, Expr pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_PLUS, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2, Expr pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_SUB, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Expr divide(Expr pParam1, Expr pParam2, Expr pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_DIV, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2, Expr pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_MULT, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Expr remainder(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_REM, pParam1, pParam2);
  }

  @Override
  protected Expr assignment(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Expr equalWithFPSemantics(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_EQ, pParam1, pParam2);
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_GT, pParam1, pParam2);
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_GEQ, pParam1, pParam2);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_LT, pParam1, pParam2);
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_LEQ, pParam1, pParam2);
  }

  @Override
  protected Expr isNaN(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISNAN, pParam1);
  }

  @Override
  protected Expr isInfinity(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISINF, pParam1);
  }

  @Override
  protected Expr isZero(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISZ, pParam1);
  }

  @Override
  protected Expr isSubnormal(Expr pParam1) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISSN, pParam1);
  }

  @Override
  protected Expr isNormal(Expr pParam) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISN, pParam);
  }

  @Override
  protected Expr isNegative(Expr pParam) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_ISNEG, pParam);
  }

  @Override
  protected Expr fromIeeeBitvectorImpl(Expr bitvector, FloatingPointType pTargetType) {
    // This is just named weird, but the CVC4 doc say this is IEEE BV -> FP
    FloatingPointConvertSort fpConvertSort = new FloatingPointConvertSort(getFPSize(pTargetType));
    Expr op = exprManager.mkConst(new FloatingPointToFPIEEEBitVector(fpConvertSort));
    return exprManager.mkExpr(op, bitvector);
  }

  @Override
  protected Expr toIeeeBitvectorImpl(Expr pNumber) {
    // TODO possible work-around: use a tmp-variable "TMP" and add an
    // additional constraint "pNumer == fromIeeeBitvectorImpl(TMP)" for it in all use-cases.
    throw new UnsupportedOperationException("FP to IEEE-BV is not supported");
  }

  @Override
  protected Expr round(Expr pFormula, FloatingPointRoundingMode pRoundingMode) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_RTI, getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
