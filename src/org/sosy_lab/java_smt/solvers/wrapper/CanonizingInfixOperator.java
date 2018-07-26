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

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;

public class CanonizingInfixOperator implements CanonizingFormula {

  private FormulaManager mgr;
  private FormulaType<?> returnType;
  private CanonizingFormula parent;
  private FunctionDeclarationKind operator;
  private CanonizingFormula left;
  private CanonizingFormula right;

  public CanonizingInfixOperator(
      FormulaManager pMgr, FunctionDeclarationKind pKind, FormulaType<?> pReturnType) {
    this(pMgr, null, pKind, pReturnType);
  }

  public CanonizingInfixOperator(
      FormulaManager pMgr,
      CanonizingFormula pParent,
      FunctionDeclarationKind pKind,
      FormulaType<?> pReturnType) {
    mgr = pMgr;
    parent = pParent;
    operator = pKind;
    returnType = pReturnType;
  }

  @Override
  public void add(CanonizingFormula pFormula) {
    if (left == null) {
      left = pFormula;
      left.setParent(this);
    } else if (right == null) {
      right = pFormula;
      right.setParent(this);
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
    CanonizingFormula copy = new CanonizingInfixOperator(mgr, operator, returnType);

    if (left != null) {
      copy.add(left.copy());
    }

    if (right != null) {
      copy.add(right.copy());
    }

    return copy;
  }

  @Override
  public BooleanFormula toFormula(FormulaManager pMgr) {
    // TODO Auto-generated method stub
    return null;
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
