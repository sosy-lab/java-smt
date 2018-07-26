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

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

public class CanonizingFormulaVisitor implements FormulaVisitor<Void> {

  private final CanonizingFormulaStore store;
  private final FormulaManager mgr;

  public CanonizingFormulaVisitor(FormulaManager pMgr) {
    mgr = pMgr;
    store = new CanonizingFormulaStore(mgr);
  }

  public CanonizingFormulaStore getStorage() {
    return store.copy();
  }

  @Override
  public Void visitFreeVariable(Formula pF, String pName) {
    store.storeVariable(pName);

    return null;
  }

  @Override
  public Void visitBoundVariable(Formula pF, int pDeBruijnIdx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Void visitConstant(Formula pF, Object pValue) {
    store.storeConstant(pValue);

    return null;
  }

  @Override
  public Void visitFunction(
      Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
    switch (pArgs.size()) {
      case 1:
      case 3:
        store.storePrefixOperator(pFunctionDeclaration.getKind(), pArgs.size());

        for (int i = 0; i < pArgs.size(); i++) {
          store.storeType(pFunctionDeclaration.getArgumentTypes().get(i));
          mgr.visit(pArgs.get(i), this);
        }
        break;
      case 2:
        store.storeInfixOperator(pFunctionDeclaration.getKind());

        store.storeType(pFunctionDeclaration.getArgumentTypes().get(0));
        mgr.visit(pArgs.get(0), this);

        store.storeType(pFunctionDeclaration.getArgumentTypes().get(1));
        mgr.visit(pArgs.get(1), this);
        break;
      default:
        // TODO: Exception/Error/Not implemented/...
    }

    store.closeOperand();

    return null;
  }

  @Override
  public Void visitQuantifier(
      BooleanFormula pF,
      Quantifier pQuantifier,
      List<Formula> pBoundVariables,
      BooleanFormula pBody) {
    // TODO Auto-generated method stub
    return null;
  }

  public void push() {
    store.push();
  }

  public void pop() {
    store.pop();
  }
}
