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

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
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
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingPrefixOperator implements CanonizingFormula {

  private FormulaManager mgr;
  private FormulaType<?> returnType;
  private FunctionDeclarationKind operator;
  private ImmutableList<CanonizingFormula> operands;

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

    if (returnType.isBitvectorType()) {
      BitvectorFormulaManager bmgr = pMgr.getBitvectorFormulaManager();
      BitvectorFormula[] bvOperands = new BitvectorFormula[operands.size()];
      for (int i = 0; i < bvOperands.length; i++) {
        bvOperands[i] = (BitvectorFormula) operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        case BV_EXTRACT:
          // FIXME: how to determine sign?
          // handle operands 1 and 2 meaningfully
          //          formula = bmgr.extract(bvOperands[0], operands.get(1), bvOperands[2], signed);
          break;
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isIntegerType()) {
      IntegerFormulaManager bmgr = pMgr.getIntegerFormulaManager();
      IntegerFormula[] bvOperands = new IntegerFormula[operands.size()];
      for (int i = 0; i < bvOperands.length; i++) {
        bvOperands[i] = (IntegerFormula) operands.get(i).toFormula(pMgr);
      }
    } else if (returnType.isFloatingPointType()) {
      FloatingPointFormulaManager bmgr = pMgr.getFloatingPointFormulaManager();
      FloatingPointFormula[] bvOperands = new FloatingPointFormula[operands.size()];
      for (int i = 0; i < bvOperands.length; i++) {
        bvOperands[i] = (FloatingPointFormula) operands.get(i).toFormula(pMgr);
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
}
