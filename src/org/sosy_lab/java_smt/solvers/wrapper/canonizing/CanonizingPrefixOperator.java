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

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingPrefixOperator implements CanonizingFormula {

  private FormulaManager mgr;
  private FormulaType<?> returnType;
  private FunctionDeclarationKind operator;
  private ImmutableList<CanonizingFormula> operands;

  private Integer hashCode = null;

  public CanonizingPrefixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      List<CanonizingFormula> pOperands,
      FormulaType<?> pReturnType) {
    mgr = pMgr;
    operator = pKind;
    operands = ImmutableList.copyOf(pOperands);
    returnType = pReturnType;
  }

  @Override
  public CanonizingFormula getOperand1() {
    return operands.get(0);
  }

  @Override
  public CanonizingFormula getOperand2() {
    return operands.get(1);
  }

  @Override
  public CanonizingFormula getOperand3() {
    return operands.get(2);
  }

  public FunctionDeclarationKind getOperator() {
    return operator;
  }

  public CanonizingFormula getOperand(int pOperand) {
    return operands.get(pOperand);
  }

  @Override
  public CanonizingFormula copy() {
    List<CanonizingFormula> operandsCopy = new ArrayList<>();
    for (int i = 0; i < operands.size(); i++) {
      operandsCopy.set(i, operands.get(i).copy());
    }

    CanonizingFormula copy =
        new CanonizingPrefixOperator(mgr, operator, operandsCopy, returnType);

    return copy;
  }

  @Override
  public Formula toFormula(FormulaManager pMgr) {
    Formula formula = null;

    if (operator == FunctionDeclarationKind.ITE) {
      BooleanFormulaManager bmgr = pMgr.getBooleanFormulaManager();
      BooleanFormula formula0 = (BooleanFormula) operands.get(0).toFormula(pMgr);
      Formula formula1 = operands.get(1).toFormula(pMgr);
      Formula formula2 = operands.get(2).toFormula(pMgr);

      return bmgr.ifThenElse(formula0, formula1, formula2);
    }

    if (returnType.isBitvectorType()) {
      BitvectorFormulaManager bmgr = pMgr.getBitvectorFormulaManager();
      BitvectorFormula[] bvOperands = new BitvectorFormula[operands.size()];
      for (int i = 0; i < bvOperands.length; i++) {
        bvOperands[i] = (BitvectorFormula) operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        case BV_EXTRACT:
          // XXX: sign seems to be irrelevant and superfluous, since not a single API-method
          // actually uses it
          formula =
              bmgr.extract(
                  bvOperands[0],
                  ((Integer) ((CanonizingConstant) operands.get(1)).getValue()),
                  ((Integer) ((CanonizingConstant) operands.get(2)).getValue()),
                  true);
          break;
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isIntegerType()) {
      IntegerFormulaManager bmgr = pMgr.getIntegerFormulaManager();
      IntegerFormula[] iOperands = new IntegerFormula[operands.size()];
      for (int i = 0; i < iOperands.length; i++) {
        iOperands[i] = (IntegerFormula) operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isFloatingPointType()) {
      FloatingPointFormulaManager bmgr = pMgr.getFloatingPointFormulaManager();
      FloatingPointFormula[] fpOperands = new FloatingPointFormula[operands.size()];
      for (int i = 0; i < fpOperands.length; i++) {
        fpOperands[i] = (FloatingPointFormula) operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        case FP_NEG:
          formula = bmgr.negate(fpOperands[0]);
          break;
        case FP_ROUND_AWAY:
          formula = bmgr.round(fpOperands[0], FloatingPointRoundingMode.NEAREST_TIES_AWAY);
          break;
        case FP_ROUND_EVEN:
          formula = bmgr.round(fpOperands[0], FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
          break;
        case FP_ROUND_NEGATIVE:
          formula = bmgr.round(fpOperands[0], FloatingPointRoundingMode.TOWARD_NEGATIVE);
          break;
        case FP_ROUND_POSITIVE:
          formula = bmgr.round(fpOperands[0], FloatingPointRoundingMode.TOWARD_POSITIVE);
          break;
        case FP_ROUND_ZERO:
          formula = bmgr.round(fpOperands[0], FloatingPointRoundingMode.TOWARD_ZERO);
          break;
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    }

    return formula;
  }

  @Override
  public CanonizingFormula canonize(CanonizingStrategy pStrategy) {
    return pStrategy.canonizePrefixOperator(
        mgr,
        operator,
        operands,
        returnType);
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
    builder.append(operator).append(" ");
    for (CanonizingFormula cF : operands) {
      builder.append("_ ( ");
      cF.toString(builder);
      builder.append(" ) ");
    }

    return builder.toString();
  }

  @Override
  public void toString(StringBuilder pBuilder) {
    pBuilder.append("( ").append(operator).append(" ");
    for (CanonizingFormula cF : operands) {
      pBuilder.append("_ ( ");
      cF.toString(pBuilder);
      pBuilder.append(" )");
    }
    pBuilder.append(" )");
  }

  @Override
  public int hashCode() {
    final int prime = 53;
    int result = 1;
    if (hashCode == null) {
      result = prime * result + ((operands == null) ? 0 : operands.hashCode());
      result = prime * result + ((operator == null) ? 0 : operator.hashCode());
      result = prime * result + ((returnType == null) ? 0 : returnType.hashCode());
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
    if (!(obj instanceof CanonizingPrefixOperator)) {
      return false;
    }
    CanonizingPrefixOperator other = (CanonizingPrefixOperator) obj;
    if (operands == null) {
      if (other.operands != null) {
        return false;
      }
    } else if (!operands.equals(other.operands)) {
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
    return true;
  }
}
