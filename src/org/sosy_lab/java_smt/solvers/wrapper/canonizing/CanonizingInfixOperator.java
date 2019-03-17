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
package org.sosy_lab.java_smt.solvers.wrapper.canonizing;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingInfixOperator implements CanonizingFormula {

  private static final long serialVersionUID = 1L;
  private transient FormulaManager mgr;
  private FormulaType<?> returnType;
  private FunctionDeclarationKind operator;
  private CanonizingFormula left;
  private CanonizingFormula right;

  private Integer hashCode = null;
  private transient Formula translated = null;

  private transient CanonizingFormula canonized = null;

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

  @SuppressWarnings({"rawtypes", "unchecked"})
  @Override
  public Formula toFormula(FormulaManager pMgr) {
    if (translated != null) {
      return translated;
    }
    FormulaType<?> innerType = left.getType();

    if (returnType.isBitvectorType() || innerType.isBitvectorType()) {
      BitvectorFormulaManager bmgr = pMgr.getBitvectorFormulaManager();
      BitvectorFormula lFormula = (BitvectorFormula) left.toFormula(pMgr);
      BitvectorFormula rFormula = (BitvectorFormula) right.toFormula(pMgr);

      switch (operator) {
        case BV_ADD:
          translated = bmgr.add(lFormula, rFormula);
          break;
        case BV_AND:
          translated = bmgr.and(lFormula, rFormula);
          break;
        case BV_ASHR:
          translated = bmgr.shiftRight(lFormula, rFormula, true);
          break;
        case BV_CONCAT:
          translated = bmgr.concat(lFormula, rFormula);
          break;
        case EQ:
        case BV_EQ:
          translated = bmgr.equal(lFormula, rFormula);
          break;
        case BV_LSHR:
          translated = bmgr.shiftRight(lFormula, rFormula, false);
          break;
        case BV_MUL:
          translated = bmgr.multiply(lFormula, rFormula);
          break;
        case BV_OR:
          translated = bmgr.or(lFormula, rFormula);
          break;
        case BV_SDIV:
          translated = bmgr.divide(lFormula, rFormula, true);
          break;
        case BV_SGE:
          translated = bmgr.greaterOrEquals(lFormula, rFormula, true);
          break;
        case BV_SGT:
          translated = bmgr.greaterThan(lFormula, rFormula, true);
          break;
        case BV_SLE:
          translated = bmgr.lessOrEquals(lFormula, rFormula, true);
          break;
        case BV_SLT:
          translated = bmgr.lessThan(lFormula, rFormula, true);
          break;
        case BV_UDIV:
          translated = bmgr.divide(lFormula, rFormula, false);
          break;
        case BV_UGE:
          translated = bmgr.greaterOrEquals(lFormula, rFormula, false);
          break;
        case BV_UGT:
          translated = bmgr.greaterThan(lFormula, rFormula, false);
          break;
        case BV_ULE:
          translated = bmgr.lessOrEquals(lFormula, rFormula, false);
          break;
        case BV_ULT:
          translated = bmgr.lessThan(lFormula, rFormula, false);
          break;
        case BV_SHL:
          translated = bmgr.shiftLeft(lFormula, rFormula);
          break;
        case BV_SUB:
          translated = bmgr.subtract(lFormula, rFormula);
          break;
        case BV_XOR:
          translated = bmgr.xor(lFormula, rFormula);
          break;
        case BV_SREM:
          translated = bmgr.modulo(lFormula, rFormula, true);
          break;
        case BV_UREM:
          translated = bmgr.modulo(lFormula, rFormula, false);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isIntegerType() || innerType.isIntegerType()) {
      IntegerFormulaManager imgr = pMgr.getIntegerFormulaManager();
      IntegerFormula lFormula = (IntegerFormula) left.toFormula(pMgr);
      IntegerFormula rFormula = (IntegerFormula) right.toFormula(pMgr);

      switch (operator) {
        case ADD:
          translated = imgr.add(lFormula, rFormula);
          break;
        case DIV:
          translated = imgr.divide(lFormula, rFormula);
          break;
        case EQ:
          translated = imgr.equal(lFormula, rFormula);
          break;
        case GT:
          translated = imgr.greaterThan(lFormula, rFormula);
          break;
        case GTE:
          translated = imgr.greaterOrEquals(lFormula, rFormula);
          break;
        case LT:
          translated = imgr.lessThan(lFormula, rFormula);
          break;
        case LTE:
          translated = imgr.lessOrEquals(lFormula, rFormula);
          break;
        case MODULO:
          translated = imgr.modulo(lFormula, rFormula);
          break;
        case MUL:
          translated = imgr.multiply(lFormula, rFormula);
          break;
        case SUB:
          translated = imgr.subtract(lFormula, rFormula);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isFloatingPointType() || innerType.isFloatingPointType()) {
      FloatingPointFormulaManager fmgr = pMgr.getFloatingPointFormulaManager();
      FloatingPointFormula lFormula = (FloatingPointFormula) left.toFormula(pMgr);
      FloatingPointFormula rFormula = (FloatingPointFormula) right.toFormula(pMgr);

      switch (operator) {
        case FP_ADD:
          translated = fmgr.add(lFormula, rFormula);
          break;
        case FP_DIV:
          translated = fmgr.divide(lFormula, rFormula);
          break;
        case EQ:
        case FP_EQ:
          translated = fmgr.equalWithFPSemantics(lFormula, rFormula);
          break;
        case FP_GE:
          translated = fmgr.greaterOrEquals(lFormula, rFormula);
          break;
        case FP_GT:
          translated = fmgr.greaterThan(lFormula, rFormula);
          break;
        case FP_LE:
          translated = fmgr.lessOrEquals(lFormula, rFormula);
          break;
        case FP_LT:
          translated = fmgr.lessThan(lFormula, rFormula);
          break;
        case FP_MUL:
          translated = fmgr.multiply(lFormula, rFormula);
          break;
        case FP_SUB:
          translated = fmgr.subtract(lFormula, rFormula);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isBooleanType() && innerType.isBooleanType()) {
      BooleanFormulaManager bmgr = pMgr.getBooleanFormulaManager();
      BooleanFormula lFormula = (BooleanFormula) left.toFormula(pMgr);
      BooleanFormula rFormula = (BooleanFormula) right.toFormula(pMgr);

      switch (operator) {
        case AND:
          translated = bmgr.and(lFormula, rFormula);
          break;
        case OR:
          translated = bmgr.or(lFormula, rFormula);
          break;
        case IMPLIES:
          translated = bmgr.implication(lFormula, rFormula);
          break;
        case XOR:
          translated = bmgr.xor(lFormula, rFormula);
          break;
        case IFF:
          translated = bmgr.equivalence(lFormula, rFormula);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isBooleanType() && innerType.isArrayType()) {
      ArrayFormulaManager amgr = pMgr.getArrayFormulaManager();
      ArrayFormula lFormula = (ArrayFormula) left.toFormula(pMgr);
      ArrayFormula rFormula = (ArrayFormula) right.toFormula(pMgr);

      switch (operator) {
        case EQ:
          translated = amgr.equivalence(lFormula, rFormula);
          break;
        default:
          throw new IllegalStateException(
              "Handling for InfixOperator " + operator + " not yet implemented.");
      }
    }

    return translated;
  }

  @Override
  public CanonizingFormula canonize(CanonizingStrategy pStrategy, CanonizingFormulaStore pCaller) {
    if (canonized == null) {
      canonized = pStrategy.canonizeInfixOperator(mgr, operator, left, right, returnType, pCaller);
    }
    return canonized;
  }

  @Override
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

  @Override
  public int hashCode() {
    final int prime = 47;
    int result = 1;
    if (hashCode == null) {
      result = prime * result + ((left == null) ? 0 : left.hashCode());
      result = prime * result + ((operator == null) ? 0 : operator.hashCode());
      result = prime * result + ((returnType == null) ? 0 : returnType.hashCode());
      result = prime * result + ((right == null) ? 0 : right.hashCode());
      hashCode = result;
    }
    return hashCode;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (!(obj instanceof CanonizingInfixOperator)) {
      return false;
    }
    CanonizingInfixOperator other = (CanonizingInfixOperator) obj;
    if (left == null) {
      if (other.left != null) {
        return false;
      }
    } else if (!left.equals(other.left)) {
      return false;
    }
    if (operator != other.operator) {
      return false;
    }
    if (returnType == null) {
      if (other.returnType != null) {
        return false;
      }
    } else if (!returnType.equals(other.returnType)) {
      return false;
    }
    if (right == null) {
      if (other.right != null) {
        return false;
      }
    } else if (!right.equals(other.right)) {
      return false;
    }
    return true;
  }
}
