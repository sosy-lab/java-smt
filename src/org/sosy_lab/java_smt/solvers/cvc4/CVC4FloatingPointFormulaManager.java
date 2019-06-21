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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.collect.ImmutableList;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.FloatingPoint;
import edu.nyu.acsys.CVC4.FloatingPointConvertSort;
import edu.nyu.acsys.CVC4.FloatingPointSize;
import edu.nyu.acsys.CVC4.FloatingPointToFPFloatingPoint;
import edu.nyu.acsys.CVC4.FloatingPointToSBV;
import edu.nyu.acsys.CVC4.Integer;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.RoundingMode;
import edu.nyu.acsys.CVC4.Type;
import java.math.BigDecimal;
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
  protected Expr makeNumberImpl(BigDecimal pN, FloatingPointType pType, Expr pRoundingMode) {
    return makeNumberImpl(pN.toString(), pType, pRoundingMode);
  }

  @Override
  protected Expr makeNumberAndRound(String pN, FloatingPointType pType, Expr pRoundingMode) {
    try {
      if (isNegativeZero(Double.valueOf(pN))) {
        return negate(
            exprManager.mkConst(
                new FloatingPoint(
                    getFPSize(pType),
                    pRoundingMode.getConstRoundingMode(),
                    Rational.fromDecimal(pN))));
      }
    } catch (NumberFormatException e) {
      // ignore and fallback to floating point from rational numbers
    }
    return exprManager.mkConst(
        new FloatingPoint(getFPSize(pType), pRoundingMode.getConstRoundingMode(), toRational(pN)));
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
        org.sosy_lab.common.rationals.Rational r =
            org.sosy_lab.common.rationals.Rational.ofString(pN);
        return new Rational(new Integer(r.getNum().toString()), new Integer(r.getDen().toString()));

      } catch (NumberFormatException e2) {
        // we cannot handle the number
        throw new NumberFormatException("invalid numeral: " + pN);
      }
    }
  }

  @Override
  protected Expr makeVariableImpl(String varName, FloatingPointType pType) {
    return exprManager.mkVar(varName, formulaCreator.getFloatingPointType(pType));
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
  protected Expr castToImpl(Expr pNumber, FormulaType<?> pTargetType, Expr pRoundingMode) {
    if (pTargetType.isFloatingPointType()) {
      FloatingPointType targetType = (FloatingPointType) pTargetType;
      FloatingPointConvertSort fpConvertSort = new FloatingPointConvertSort(getFPSize(targetType));
      Expr op = exprManager.mkConst(new FloatingPointToFPFloatingPoint(fpConvertSort));
      return exprManager.mkExpr(op, pRoundingMode, pNumber);

    } else if (pTargetType.isBitvectorType()) {
      BitvectorType targetType = (BitvectorType) pTargetType;
      Expr op = exprManager.mkConst(new FloatingPointToSBV(targetType.getSize()));
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
      return castToImpl(pNumber, pTargetType, pRoundingMode);
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
  protected Expr fromIeeeBitvectorImpl(Expr pNumber, FloatingPointType pTargetType) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_FP, pNumber);
  }

  @Override
  protected Expr toIeeeBitvectorImpl(Expr pNumber) {
    return exprManager.mkExpr(Kind.FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, pNumber);
  }

  @Override
  protected Expr round(Expr pFormula, FloatingPointRoundingMode pRoundingMode) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }
}
