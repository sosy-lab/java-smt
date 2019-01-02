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

import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class CanonizingInfixOperator implements CanonizingFormula {

  private FormulaManager mgr;
  private FormulaType<?> returnType;
  private FunctionDeclarationKind operator;
  private CanonizingFormula left;
  private CanonizingFormula right;

  public CanonizingInfixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      CanonizingFormula pLeft,
      CanonizingFormula pRight,
      FormulaType<?> pReturnType) {
    mgr = pMgr;
    operator = pKind;
    left = pLeft;
    right = pRight;
    returnType = pReturnType;
  }

  @Override
  public CanonizingFormula getOperand1() {
    return left;
  }

  @Override
  public CanonizingFormula getOperand2() {
    return right;
  }

  public FunctionDeclarationKind getOperator() {
    return operator;
  }

  @Override
  public CanonizingFormula copy() {
    CanonizingFormula copy =
        new CanonizingInfixOperator(mgr, operator, left.copy(), right.copy(), returnType);

    return copy;
  }

  @Override
  public Formula toFormula(FormulaManager pMgr) {
    Formula formula = null;

    if (returnType.isBitvectorType()) {
      BitvectorFormulaManager bmgr = pMgr.getBitvectorFormulaManager();
      BitvectorFormula lFormula = (BitvectorFormula) left.toFormula(pMgr);
      BitvectorFormula rFormula = (BitvectorFormula) right.toFormula(pMgr);

      switch (operator) {
        case BV_ADD:
          formula = bmgr.add(lFormula, rFormula);
          break;
        case BV_AND:
          formula = bmgr.and(lFormula, rFormula);
          break;
        case BV_ASHR:
          formula = bmgr.shiftRight(lFormula, rFormula, true);
          break;
        case BV_CONCAT:
          formula = bmgr.concat(lFormula, rFormula);
          break;
          // FIXME: returnType.isBoolean() ?
        case BV_EQ:
          formula = bmgr.equal(lFormula, rFormula);
          break;
          // FIXME - end
        case BV_LSHR:
          formula = bmgr.shiftRight(lFormula, rFormula, false);
          break;
        case BV_MUL:
          formula = bmgr.multiply(lFormula, rFormula);
          break;
        case BV_OR:
          formula = bmgr.or(lFormula, rFormula);
          break;
        case BV_SDIV:
          formula = bmgr.divide(lFormula, rFormula, true);
          break;
          // FIXME: returnType.isBoolean() ?
        case BV_SGE:
          formula = bmgr.greaterOrEquals(lFormula, rFormula, true);
          break;
        case BV_SGT:
          formula = bmgr.greaterThan(lFormula, rFormula, true);
          break;
        case BV_SLE:
          formula = bmgr.lessOrEquals(lFormula, rFormula, true);
          break;
        case BV_SLT:
          formula = bmgr.lessThan(lFormula, rFormula, true);
          break;
          // FIXME - end
        case BV_UDIV:
          formula = bmgr.divide(lFormula, rFormula, false);
          break;
          // FIXME: returnType.isBoolean() ?
        case BV_UGE:
          formula = bmgr.greaterOrEquals(lFormula, rFormula, false);
          break;
        case BV_UGT:
          formula = bmgr.greaterThan(lFormula, rFormula, false);
          break;
        case BV_ULE:
          formula = bmgr.lessOrEquals(lFormula, rFormula, false);
          break;
        case BV_ULT:
          formula = bmgr.lessThan(lFormula, rFormula, false);
          break;
          // FIXME - end
        case BV_SHL:
          formula = bmgr.shiftLeft(lFormula, rFormula);
          break;
        case BV_SUB:
          formula = bmgr.subtract(lFormula, rFormula);
          break;
        case BV_XOR:
          formula = bmgr.xor(lFormula, rFormula);
          break;
        case BV_SREM:
          formula = bmgr.modulo(lFormula, rFormula, true);
          break;
        case BV_UREM:
          formula = bmgr.modulo(lFormula, rFormula, false);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isIntegerType()) {
      IntegerFormulaManager imgr = pMgr.getIntegerFormulaManager();
      IntegerFormula lFormula = (IntegerFormula) left.toFormula(pMgr);
      IntegerFormula rFormula = (IntegerFormula) right.toFormula(pMgr);

      switch (operator) {
        case ADD:
          formula = imgr.add(lFormula, rFormula);
          break;
        case DIV:
          formula = imgr.divide(lFormula, rFormula);
          break;
        case EQ:
          formula = imgr.equal(lFormula, rFormula);
          break;
        case GT:
          formula = imgr.greaterThan(lFormula, rFormula);
          break;
        case GTE:
          formula = imgr.greaterOrEquals(lFormula, rFormula);
          break;
        case LT:
          formula = imgr.lessThan(lFormula, rFormula);
          break;
        case LTE:
          formula = imgr.lessOrEquals(lFormula, rFormula);
          break;
        case MODULO:
          formula = imgr.modulo(lFormula, rFormula);
          break;
        case MUL:
          formula = imgr.multiply(lFormula, rFormula);
          break;
        case SUB:
          formula = imgr.subtract(lFormula, rFormula);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isFloatingPointType()) {
      FloatingPointFormulaManager fmgr = pMgr.getFloatingPointFormulaManager();
      FloatingPointFormula lFormula = (FloatingPointFormula) left.toFormula(pMgr);
      FloatingPointFormula rFormula = (FloatingPointFormula) right.toFormula(pMgr);

      switch (operator) {
        case FP_ADD:
          formula = fmgr.add(lFormula, rFormula);
          break;
        case FP_DIV:
          formula = fmgr.divide(lFormula, rFormula);
          break;
        case FP_EQ:
          formula = fmgr.equalWithFPSemantics(lFormula, rFormula);
          break;
        case FP_GE:
          formula = fmgr.greaterOrEquals(lFormula, rFormula);
          break;
        case FP_GT:
          formula = fmgr.greaterThan(lFormula, rFormula);
          break;
        case FP_LE:
          formula = fmgr.lessOrEquals(lFormula, rFormula);
          break;
        case FP_LT:
          formula = fmgr.lessThan(lFormula, rFormula);
          break;
        case FP_MUL:
          formula = fmgr.multiply(lFormula, rFormula);
          break;
        case FP_SUB:
          formula = fmgr.subtract(lFormula, rFormula);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    }

    return formula;
  }

  @Override
  public CanonizingFormula canonize() {
    return CanonizingStrategy.canonizeInfixOperator(mgr, operator, left, right, returnType);
  }

  public FormulaType<?> getType() {
    return returnType;
  }

  @Override
  public FormulaManager getFormulaManager() {
    return mgr;
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    if (left != null) {
      left.toString(builder);
    }
    builder.append(" ").append(operator).append(" ");
    if (right != null) {
      right.toString(builder);
    }

    return builder.toString();
  }

  @Override
  public void toString(StringBuilder pBuilder) {
    pBuilder.append("( ");
    if (left != null) {
      left.toString(pBuilder);
    }
    pBuilder.append(" ").append(operator).append(" ");
    if (right != null) {
      right.toString(pBuilder);
    }
    pBuilder.append(" )");
  }
}
