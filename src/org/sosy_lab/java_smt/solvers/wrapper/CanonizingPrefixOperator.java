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

import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

public class CanonizingPrefixOperator implements CanonizingFormula {

  private FormulaManager mgr;
  private FormulaType<?> returnType;
  private FunctionDeclarationKind operator;
  private List<CanonizingFormula> operands;
  private int operand = 0;
  private int operandSize = 0;

  private CanonizingFormula parent;

  public CanonizingPrefixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      int pOperands,
      FormulaType<?> pReturnType) {
    mgr = pMgr;
    operator = pKind;
    operandSize = pOperands;
    operands = new ArrayList<>(pOperands);
    returnType = pReturnType;
  }

  private CanonizingPrefixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      int pOperand,
      List<CanonizingFormula> pOperands,
      int pOperandSize,
      FormulaType<?> pReturnType) {
    mgr = pMgr;
    operator = pKind;
    operands = pOperands;
    operand = pOperand;
    operandSize = pOperandSize;
    returnType = pReturnType;
  }

  @Override
  public void add(CanonizingFormula pFormula) {
    if (operand < operandSize) {
      operands.add(operand++, pFormula);
      pFormula.setParent(this);
    } else {
      assert false;
    }
  }

  @Override
  public void setParent(CanonizingFormula pFormula) {
    parent = pFormula;
  }

  @Override
  public CanonizingFormula getParent() {
    return parent;
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
    for (int i = 0; i < operand; i++) {
      operandsCopy.set(i, operands.get(i).copy());
    }

    CanonizingFormula copy =
        new CanonizingPrefixOperator(mgr, operator, operand, operandsCopy, operandSize, returnType);

    return copy;
  }

  @Override
  public BooleanFormula toFormula(FormulaManager pMgr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CanonizingFormula canonize() {
    // TODO Auto-generated method stub
    return null;
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
