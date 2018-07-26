/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper;

import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

public class CanonizingStrategy {

  public static CanonizingFormula canonizeInfixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pOperator,
      CanonizingFormula pLeft,
      CanonizingFormula pRight,
      FormulaType<?> pReturnType) {
    FunctionDeclarationKind operator = pOperator;
    CanonizingFormula left = pLeft.canonize();
    CanonizingFormula right = pRight.canonize();

    if (isGreaterOp(pOperator)) {
      // TODO: find meaningful handling of arrays
      if (!pReturnType.isRationalType()) {
        operator = FunctionDeclarationKind.LT;
      } else {
        operator = FunctionDeclarationKind.LTE;
      }
      CanonizingFormula tmp = left;
      left = right;
      right = tmp;
    }

    // TODO: find meaningful handling of arrayslea
    if (isOrEqualOp(pOperator) && !pReturnType.isRationalType()) {
      Object epsilon = getMinimumSummand(pMgr, pReturnType);
      right = add(right, epsilon, pReturnType);
    }

    CanonizingInfixOperator result = new CanonizingInfixOperator(pMgr, operator, pReturnType);
    result.add(left);
    result.add(right);

    return result;
  }

  private static CanonizingFormula add(
      CanonizingFormula pRight, Object pEpsilon, FormulaType<?> pReturnType) {
    if (pReturnType.isIntegerType()) {
      // TODO: traverse pRight to find a constant to which to add pEpsilon fully or a
      // Integer.sum(int a, int b);
    }
    if (pReturnType.isBitvectorType()) {
      // TODO: traverse pRight to find a constant to which to add pEpsilon fully or a
    }
    if (pReturnType.isFloatingPointType()) {
      // TODO: traverse pRight to find a constant to which to add pEpsilon fully or a
    }
    if (pReturnType.isArrayType()) {
      // TODO: for arrays we have to traverse the correct operand to determine the type
    }
    if (pReturnType.isRationalType()) {
      // TODO: traverse pRight to find a constant to which to add pEpsilon fully or a
    }
    return null;
  }

  private static Object getMinimumSummand(FormulaManager pMgr, FormulaType<?> pReturnType) {
    if (pReturnType.isIntegerType()) {
      return Integer.valueOf(1);
    }
    if (pReturnType.isBitvectorType()) {
      int length = ((FormulaType.BitvectorType) pReturnType).getSize();
      return pMgr.getBitvectorFormulaManager().makeBitvector(length, 1);
    }
    if (pReturnType.isFloatingPointType()) {
      // TODO
    }
    if (pReturnType.isArrayType()) {
      // TODO: for arrays we have to traverse the correct operand to determine the type
    }
    if (pReturnType.isRationalType()) {
      // FIXME: for this one, there is no meaningful solution, so 'lessThanOrEquals' should be kept
      // as such
    }
    return null;
  }

  private static boolean isOrEqualOp(FunctionDeclarationKind pO) {
    boolean answer = false;
    if (pO == FunctionDeclarationKind.GTE
        || pO == FunctionDeclarationKind.FP_GE
        || pO == FunctionDeclarationKind.BV_SGE
        || pO == FunctionDeclarationKind.BV_UGE) {
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
