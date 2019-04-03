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
package org.sosy_lab.java_smt.solvers.wrapper.strategy;

import com.google.errorprone.annotations.Immutable;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingConstant;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormula;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormulaStore;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingInfixOperator;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingPrefixOperator;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingVariable;

@Immutable
public class ReorderingStrategy implements CanonizingStrategy {

  @Override
  public CanonizingFormula canonizeInfixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pOperator,
      CanonizingFormula pLeft,
      CanonizingFormula pRight,
      FormulaType<?> pReturnType,
      CanonizingFormulaStore pCaller) {
    FunctionDeclarationKind operator = pOperator;
    CanonizingFormula left = pLeft.canonize(this, pCaller);
    CanonizingFormula right = pRight.canonize(this, pCaller);
    boolean transformationPossible =
        isTransformationPossible(left.getType(), right.getType());
    FormulaType<?> type = determineType(left.getType(), right.getType());
    CanonizingInfixOperator result = null;

    if (isInequalityOrEquality(pOperator)) {
      if (isLesserOp(pOperator)) {
        if (transformationPossible || isOrEqualOp(pOperator)) {
          operator = getGreaterEqualsOp(type, signedOperator(operator));
        } else {
          operator = getGreaterOp(type, signedOperator(operator));
        }
        CanonizingFormula tmp = left;
        left = right;
        right = tmp;
      }

      left =
          CanonizingInfixOperator.getInstance(
              pMgr,
              getSubtractionOperator(left.getType()),
              left,
              right,
              type);
      right = CanonizingConstant.getInstance(pMgr, 0, type);

      if (transformationPossible && !isOrEqualOp(pOperator)) {
        CanonizingConstant epsilon = getMinimumSummand(pMgr, type);
        left = add(pMgr, left, negateConstant(epsilon), type);
      }

      result =
          CanonizingInfixOperator.getInstance(pMgr, operator, left, right, pReturnType);

      if (pReturnType.isBooleanType() && type.isFloatingPointType()) {
        // for cases that result in a transformation like: inf - inf == 0, which translates to nan
        // ==
        // 0 -> false, while the original inf == inf results in true
        List<CanonizingFormula> operand = new ArrayList<>();
        operand.add(result);
        CanonizingPrefixOperator compareToNan =
            CanonizingPrefixOperator
                .getInstance(
                pMgr,
                FunctionDeclarationKind.FP_IS_NAN,
                operand,
                pReturnType);
        result =
            CanonizingInfixOperator.getInstance(
                pMgr,
                FunctionDeclarationKind.OR,
                result,
                compareToNan,
                pReturnType);
      }
    } else {
      // arithmetical or logical operators where one can possibly reorder variables.
      // TODO: implement variable-reordering according to their count
    }

    if (result == null) {
      result = CanonizingInfixOperator.getInstance(pMgr, pOperator, pLeft, pRight, pReturnType);
    }

    return result;
  }

  private boolean isInequalityOrEquality(FunctionDeclarationKind pOperator) {
    return isLesserOp(pOperator)
        || isOrEqualOp(pOperator)
        || isGreaterOp(pOperator)
        || isEqualOp(pOperator);
  }

  private FunctionDeclarationKind getSubtractionOperator(FormulaType<?> pType) {
    if (pType.isIntegerType() || pType.isRationalType()) {
      return FunctionDeclarationKind.SUB;
    }
    if (pType.isBitvectorType()) {
      return FunctionDeclarationKind.BV_SUB;
    }
    if (pType.isFloatingPointType()) {
      return FunctionDeclarationKind.FP_SUB;
    }
    // TODO: Exception or something like this
    return null;
  }

  private FormulaType<?> determineType(FormulaType<?> pType0, FormulaType<?> pType1) {
    FormulaType<?> type0 = CanonizingFormula.recursivelyLookUpArray(pType0);
    FormulaType<?> type1 = CanonizingFormula.recursivelyLookUpArray(pType1);

    if (type0.equals(type1)
        || (type0.isBitvectorType() && type1.isBitvectorType())
        || (type0.isFloatingPointType() && type1.isFloatingPointType())) {
      return getGreaterType(type0, type1);
    }
    // TODO: what to do in case of differing types?
    return null;
  }

  private FormulaType<?> getGreaterType(FormulaType<?> pType0, FormulaType<?> pType1) {
    if (pType0.isBitvectorType() && pType1.isBitvectorType()) {
      int size0 = ((FormulaType.BitvectorType) pType0).getSize();
      int size1 = ((FormulaType.BitvectorType) pType1).getSize();

      return (size0 > size1) ? pType0 : pType1;
    }
    if (pType0.isFloatingPointType() && pType1.isFloatingPointType()) {
      int expSize0 = ((FormulaType.FloatingPointType) pType0).getExponentSize();
      int expSize1 = ((FormulaType.FloatingPointType) pType1).getExponentSize();
      if (expSize0 > expSize1) {
        return pType0;
      } else if (expSize1 > expSize0) {
        return pType1;
      } else {
        int manSize0 = ((FormulaType.FloatingPointType) pType0).getMantissaSize();
        int manSize1 = ((FormulaType.FloatingPointType) pType1).getMantissaSize();

        return (manSize0 > manSize1) ? pType0 : pType1;
      }
    }
    return pType0;
  }

  private boolean isTransformationPossible(FormulaType<?> pType0, FormulaType<?> pType1) {
    boolean result = true;

    pType0 = CanonizingFormula.recursivelyLookUpArray(pType0);
    pType1 = CanonizingFormula.recursivelyLookUpArray(pType1);

    result &= !pType0.isRationalType();
    result &= !pType1.isRationalType();
    result &= !pType0.isBitvectorType();
    result &= !pType1.isBitvectorType();

    return result;
  }

  private boolean signedOperator(FunctionDeclarationKind pOperator) {
    return pOperator == FunctionDeclarationKind.BV_SLE
        || pOperator == FunctionDeclarationKind.BV_SLT;
  }

  private FunctionDeclarationKind
      getGreaterEqualsOp(FormulaType<?> pType, boolean isSigned) {
    pType = CanonizingFormula.recursivelyLookUpArray(pType);
    if (pType.isFloatingPointType()) {
      return FunctionDeclarationKind.FP_GE;
    }
    if (pType.isBitvectorType()) {
      return isSigned ? FunctionDeclarationKind.BV_SGE : FunctionDeclarationKind.BV_UGE;
    }
    return FunctionDeclarationKind.GTE;
  }

  private FunctionDeclarationKind
      getGreaterOp(FormulaType<?> pType, boolean isSigned) {
    pType = CanonizingFormula.recursivelyLookUpArray(pType);
    if (pType.isFloatingPointType()) {
      return FunctionDeclarationKind.FP_GT;
    }
    if (pType.isBitvectorType()) {
      return isSigned ? FunctionDeclarationKind.BV_SGT : FunctionDeclarationKind.BV_UGT;
    }
    return FunctionDeclarationKind.GT;
  }

  private CanonizingConstant negateConstant(CanonizingConstant pConstant) {
    Object value = null;
    FormulaType<?> type = pConstant.getType();

    if (type.isIntegerType()) {
      value = ((long) pConstant.getValue()) * -1;
    } else if (type.isFloatingPointType()) {
      if (type.equals(FormulaType.getSinglePrecisionFloatingPointType())) {
        value = ((float) pConstant.getValue()) * -1;
      } else if (type.equals(FormulaType.getDoublePrecisionFloatingPointType())) {
        value = ((double) pConstant.getValue()) * -1;
      } else {
        throw new IllegalArgumentException("Type " + type + " is not fully implemented, yet.");
      }
    }
    return CanonizingConstant.getInstance(pConstant.getFormulaManager(), value, type);
  }

  private static CanonizingFormula add(
      FormulaManager pMgr,
      CanonizingFormula pFormula,
      CanonizingConstant pEpsilon,
      FormulaType<?> pReturnType) {
    FunctionDeclarationKind kind = null;
    CanonizingFormula result = null;

    if (pEpsilon.getType().isIntegerType()) {
      kind = FunctionDeclarationKind.ADD;
    }
    if (pEpsilon.getType().isBitvectorType()) {
      kind = FunctionDeclarationKind.BV_ADD;
    }
    if (pEpsilon.getType().isFloatingPointType()) {
      kind = FunctionDeclarationKind.FP_ADD;
    }

    if (pFormula instanceof CanonizingVariable) {
      CanonizingInfixOperator operator =
          CanonizingInfixOperator.getInstance(pMgr, kind, pFormula, pEpsilon, pReturnType);

      result = operator;
    } else if (pFormula instanceof CanonizingConstant) {
      Object value = null;

      if (pReturnType.isIntegerType() || pReturnType.isBitvectorType()) {
        value = ((long) ((CanonizingConstant) pFormula).getValue()) + ((int) pEpsilon.getValue());
      } else if (pReturnType.isFloatingPointType()) {
        if (pReturnType.equals(FormulaType.getSinglePrecisionFloatingPointType())) {
          value =
              ((float) ((CanonizingConstant) pFormula).getValue()) + ((float) pEpsilon.getValue());
        } else if (pReturnType.equals(FormulaType.getDoublePrecisionFloatingPointType())) {
          value =
              ((double) ((CanonizingConstant) pFormula).getValue())
                  + ((double) pEpsilon.getValue());
        } else {
          throw new IllegalArgumentException(
              "Type " + pReturnType + " is not fully implemented, yet.");
        }
      }
      result = CanonizingConstant.getInstance(pMgr, value, pReturnType);
    } else {
      result = add(pMgr, pFormula.getOperand1(), pEpsilon, pReturnType);
    }

    return result;
  }

  // FIXME: Bitvector-Overflow and FloatingPoint-Special-Values (Infinitiy)
  private static CanonizingConstant
      getMinimumSummand(FormulaManager pMgr, FormulaType<?> pReturnType) {
    if (pReturnType.isIntegerType()) {
      return CanonizingConstant.getInstance(pMgr, Integer.valueOf(1), pReturnType);
    }
    if (pReturnType.isFloatingPointType()) {
      double value;
      if (pReturnType.equals(FormulaType.getSinglePrecisionFloatingPointType())) {
        // 1 / (2 ^ 149) is the smallest IEEE single precision floating point number, that is still
        // greater than 0
        value = Math.pow(2, -149);
      } else if (pReturnType.equals(FormulaType.getDoublePrecisionFloatingPointType())) {
        // 1 / (2 ^ 1074) is the smallest IEEE double precision floating point number, that is still
        // greater than 0
        value = Math.pow(2, -1074);
      } else {
        throw new IllegalArgumentException(
            "Type " + pReturnType + " is not fully implemented, yet.");
      }
      return CanonizingConstant.getInstance(pMgr, value, pReturnType);
    }
    if (pReturnType.isArrayType()) {
      return getMinimumSummand(
          pMgr,
          ((FormulaType.ArrayFormulaType<?, ?>) pReturnType).getElementType());
    }
    return null;
  }

  private static boolean isEqualOp(FunctionDeclarationKind pO) {
    boolean answer = false;
    if (pO == FunctionDeclarationKind.EQ
        || pO == FunctionDeclarationKind.BV_EQ
        || pO == FunctionDeclarationKind.FP_EQ) {
      answer = true;
    }
    return answer;
  }

  private static boolean isOrEqualOp(FunctionDeclarationKind pO) {
    boolean answer = false;
    if (pO == FunctionDeclarationKind.LTE
        || pO == FunctionDeclarationKind.FP_LE
        || pO == FunctionDeclarationKind.BV_SLE
        || pO == FunctionDeclarationKind.BV_ULE) {
      answer = true;
    }
    return answer;
  }

  private static boolean isLesserOp(FunctionDeclarationKind pO) {
    boolean answer = false;
    if (pO == FunctionDeclarationKind.LT
        || pO == FunctionDeclarationKind.LTE
        || pO == FunctionDeclarationKind.FP_LT
        || pO == FunctionDeclarationKind.FP_LE
        || pO == FunctionDeclarationKind.BV_SLT
        || pO == FunctionDeclarationKind.BV_SLE
        || pO == FunctionDeclarationKind.BV_ULT
        || pO == FunctionDeclarationKind.BV_ULE) {
      answer = true;
    }
    return answer;
  }

  private static boolean isGreaterOp(FunctionDeclarationKind pO) {
    boolean answer = false;
    if (pO == FunctionDeclarationKind.GT
        || pO == FunctionDeclarationKind.GTE
        || pO == FunctionDeclarationKind.FP_GT
        || pO == FunctionDeclarationKind.FP_GE
        || pO == FunctionDeclarationKind.BV_SGT
        || pO == FunctionDeclarationKind.BV_SGE
        || pO == FunctionDeclarationKind.BV_UGT
        || pO == FunctionDeclarationKind.BV_UGE) {
      answer = true;
    }
    return answer;
  }
}
