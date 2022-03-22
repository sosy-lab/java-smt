// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.collect.ImmutableList;
import io.github.cvc5.api.CVC5ApiException;
import io.github.cvc5.api.Kind;
import io.github.cvc5.api.Op;
import io.github.cvc5.api.RoundingMode;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.math.BigDecimal;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

public class CVC5FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;
  private final Term roundingMode;

  protected CVC5FloatingPointFormulaManager(
      CVC5FormulaCreator pCreator, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(pCreator);
    solver = pCreator.getEnv();
    roundingMode = getRoundingModeImpl(pFloatingPointRoundingMode);
  }

  @Override
  protected Term getDefaultRoundingMode() {
    return roundingMode;
  }

  @Override
  protected Term getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    switch (pFloatingPointRoundingMode) {
      case NEAREST_TIES_TO_EVEN:
        return solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN);
      case NEAREST_TIES_AWAY:
        return solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
      case TOWARD_POSITIVE:
        return solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE);
      case TOWARD_NEGATIVE:
        return solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE);
      case TOWARD_ZERO:
        return solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_ZERO);
      default:
        throw new AssertionError(
            "Unexpected rounding mode encountered: " + pFloatingPointRoundingMode);
    }
  }

  @Override
  protected Term makeNumberImpl(double pN, FloatingPointType pType, Term pRoundingMode) {
    return makeNumberImpl(Double.toString(pN), pType, pRoundingMode);
  }

  @Override
  protected Term makeNumberAndRound(String pN, FloatingPointType pType, Term pRoundingMode) {
    try {
      Rational rationalValue = toRational(pN);
      Op realToFp =
          solver.mkOp(
              Kind.FLOATINGPOINT_TO_FP_REAL, pType.getExponentSize(), pType.getMantissaSize() + 1);
      return solver.mkTerm(realToFp, pRoundingMode, solver.mkReal(rationalValue.toString()));
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid floating point with exponent size "
              + pType.getExponentSize()
              + ", mantissa size "
              + pType.getMantissaSize()
              + " and value "
              + pN
              + ".",
          e);
    }

  }

  /**
   * Try to convert a String numeral into a Rational.
   *
   * <p>If we do not check all invalid formatted numbers in our own code, CVC5 will fail hard and
   * immediately terminate the whole program.
   */
  private Rational toRational(String pN) throws NumberFormatException {
    try {
      // first try something like -123.567
      return Rational.ofBigDecimal(new BigDecimal(pN));

    } catch (NumberFormatException e1) {
      try {
        // then try something like -123/456
        return org.sosy_lab.common.rationals.Rational.ofString(pN);

      } catch (NumberFormatException e2) {
        // we cannot handle the number
        throw new NumberFormatException("invalid numeral: " + pN);
      }
    }
  }

  @Override
  protected Term makeVariableImpl(String varName, FloatingPointType pType) {
    return formulaCreator.makeVariable(formulaCreator.getFloatingPointType(pType), varName);
  }

  @Override
  protected Term makePlusInfinityImpl(FloatingPointType pType) {
    try {
      // So this should be mkFloatingPointPosInf() but that does not exists, so i guess it was
      // renamed.
      return solver.mkPosInf(pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid positive floating point infinity with exponent size "
              + pType.getExponentSize()
              + " and mantissa size "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  @Override
  protected Term makeMinusInfinityImpl(FloatingPointType pType) {
    try {
      // So this should be mkFloatingPointNegInf() but that does not exists, so i guess it was
      // renamed.
      return solver.mkNegInf(pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid negative floating point infinity with exponent size "
              + pType.getExponentSize()
              + " and mantissa size "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  @Override
  protected Term makeNaNImpl(FloatingPointType pType) {
    try {
      return solver.mkNaN(pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid NaN with exponent size "
              + pType.getExponentSize()
              + " and mantissa size "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  // FP -> other type
  @Override
  protected Term castToImpl(Term pNumber, FormulaType<?> pTargetType, Term pRoundingMode) {
    try {
      if (pTargetType.isFloatingPointType()) {
        Op fpToFp =
            solver.mkOp(
                Kind.FLOATINGPOINT_TO_FP_FLOATINGPOINT,
                ((FloatingPointType) pTargetType).getExponentSize(),
                ((FloatingPointType) pTargetType).getMantissaSize() + 1);
        return solver.mkTerm(fpToFp, pRoundingMode, pNumber);

      } else if (pTargetType.isBitvectorType()) {
        BitvectorType targetType = (BitvectorType) pTargetType;
        Op operation = solver.mkOp(Kind.FLOATINGPOINT_TO_SBV, targetType.getSize());
        return solver.mkTerm(operation, pRoundingMode, pNumber);

      } else if (pTargetType.isRationalType()) {
        return solver.mkTerm(Kind.FLOATINGPOINT_TO_REAL, pNumber);

      } else {
        return genericCast(pNumber, pTargetType);
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid cast from "
              + pNumber
              + " into a "
              + pTargetType
              + ". Check that the target type can hold the source type. (Note: for target FP types 1 bit is missing in this debug message)",
          e);
    }
  }

  // other type -> FP
  @Override
  protected Term castFromImpl(
      Term pNumber, boolean pSigned, FloatingPointType pTargetType, Term pRoundingMode) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);
    try {
      if (formulaType.isFloatingPointType()) {
        return castToImpl(pNumber, pTargetType, pRoundingMode);

      } else if (formulaType.isRationalType()) {
        Op realToFp =
            solver.mkOp(
                Kind.FLOATINGPOINT_TO_FP_REAL,
                pTargetType.getExponentSize(),
                pTargetType.getMantissaSize() + 1);

        return solver.mkTerm(realToFp, pRoundingMode, pNumber);

      } else if (formulaType.isBitvectorType()) {
        if (pSigned) {
          Op realToSBv =
              solver.mkOp(
                  Kind.FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
                  pTargetType.getExponentSize(),
                  pTargetType.getMantissaSize() + 1);
          return solver.mkTerm(realToSBv, pRoundingMode, pNumber);
        } else {
          Op realToUBv =
              solver.mkOp(
                  Kind.FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
                  pTargetType.getExponentSize(),
                  pTargetType.getMantissaSize() + 1);
          return solver.mkTerm(realToUBv, pRoundingMode, pNumber);
        }

      } else {
        Op realToGeneric =
            solver.mkOp(
                Kind.FLOATINGPOINT_TO_FP_GENERIC,
                pTargetType.getExponentSize(),
                pTargetType.getMantissaSize() + 1);
        return solver.mkTerm(realToGeneric, pRoundingMode, pNumber);
        // old version; revert to it if generic fails
        // return genericCast(pNumber, pTargetType);
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid cast from "
              + pNumber
              + " into a FloatingPoint with exponent size "
              + pTargetType.getExponentSize()
              + " and mantissa size "
              + pTargetType.getMantissaSize()
              + ".",
          e);
    }
  }

  private Term genericCast(Term pNumber, FormulaType<?> pTargetType) {
    Sort type = pNumber.getSort();

    FormulaType<?> argType = getFormulaCreator().getFormulaType(pNumber);
    Term castFuncDecl =
        getFormulaCreator()
            .declareUFImpl(
                "__cast_" + argType + "_to_" + pTargetType,
                toSolverType(pTargetType),
                ImmutableList.of(type));
    return solver.mkTerm(Kind.APPLY_UF, castFuncDecl, pNumber);
  }

  @Override
  protected Term negate(Term pParam1) {
    return solver.mkTerm(Kind.FLOATINGPOINT_NEG, pParam1);
  }

  @Override
  protected Term abs(Term pParam1) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ABS, pParam1);
  }

  @Override
  protected Term max(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_MAX, pParam1, pParam2);
  }

  @Override
  protected Term min(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_MIN, pParam1, pParam2);
  }

  @Override
  protected Term sqrt(Term pParam1, Term pRoundingMode) {
    return solver.mkTerm(Kind.FLOATINGPOINT_SQRT, pRoundingMode, pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2, Term pRoundingMode) {
    return solver.mkTerm(Kind.PLUS, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2, Term pRoundingMode) {
    return solver.mkTerm(Kind.FLOATINGPOINT_SUB, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term divide(Term pParam1, Term pParam2, Term pRoundingMode) {
    return solver.mkTerm(Kind.FLOATINGPOINT_DIV, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2, Term pRoundingMode) {
    return solver.mkTerm(Kind.FLOATINGPOINT_MULT, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term assignment(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term equalWithFPSemantics(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_EQ, pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_GT, pParam1, pParam2);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_GEQ, pParam1, pParam2);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_LT, pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.FLOATINGPOINT_LEQ, pParam1, pParam2);
  }

  @Override
  protected Term isNaN(Term pParam1) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ISNAN, pParam1);
  }

  @Override
  protected Term isInfinity(Term pParam1) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ISINF, pParam1);
  }

  @Override
  protected Term isZero(Term pParam1) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ISZ, pParam1);
  }

  @Override
  protected Term isSubnormal(Term pParam1) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ISSN, pParam1);
  }

  @Override
  protected Term isNormal(Term pParam) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ISN, pParam);
  }

  @Override
  protected Term isNegative(Term pParam) {
    return solver.mkTerm(Kind.FLOATINGPOINT_ISNEG, pParam);
  }

  @Override
  protected Term fromIeeeBitvectorImpl(Term pNumber, FloatingPointType pTargetType) {
    return solver.mkTerm(Kind.FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, pNumber);
  }

  @Override
  protected Term toIeeeBitvectorImpl(Term pNumber) {
    // TODO possible work-around: use a tmp-variable "TMP" and add an
    // additional constraint "pNumer == fromIeeeBitvectorImpl(TMP)" for it in all use-cases.
    throw new UnsupportedOperationException("FP to IEEE-BV is not supported");
  }

  @Override
  protected Term round(Term pFormula, FloatingPointRoundingMode pRoundingMode) {
    return solver.mkTerm(Kind.FLOATINGPOINT_RTI, getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
