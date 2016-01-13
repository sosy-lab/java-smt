/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Function;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

final class RecursiveFormulaVisitor implements FormulaVisitor<TraversalProcess> {

  private final Set<Formula> seen = new HashSet<>();
  private final Deque<Formula> toVisit = new ArrayDeque<>();

  private final FormulaVisitor<TraversalProcess> delegate;

  RecursiveFormulaVisitor(FormulaVisitor<TraversalProcess> pDelegate) {
    delegate = checkNotNull(pDelegate);
  }

  void addToQueue(Formula f) {
    if (seen.add(f)) {
      toVisit.push(f);
    }
  }

  boolean isQueueEmpty() {
    return toVisit.isEmpty();
  }

  Formula pop() {
    return toVisit.pop();
  }

  @Override
  public TraversalProcess visitFreeVariable(Formula pF, String pName) {
    return delegate.visitFreeVariable(pF, pName);
  }

  @Override
  public TraversalProcess visitBoundVariable(Formula pF, String pName, int pDeBruijnIdx) {
    return delegate.visitBoundVariable(pF, pName, pDeBruijnIdx);
  }

  @Override
  public TraversalProcess visitConstant(Formula pF, Object pValue) {
    return delegate.visitConstant(pF, pValue);
  }

  @Override
  public TraversalProcess visitFuncApp(
      Formula pF,
      List<Formula> pArgs,
      FuncDecl pFunctionDeclaration,
      Function<List<Formula>, Formula> pNewApplicationConstructor) {
    TraversalProcess result =
        delegate.visitFuncApp(pF, pArgs, pFunctionDeclaration, pNewApplicationConstructor);
    if (result == TraversalProcess.CONTINUE) {
      for (Formula arg : pArgs) {
        addToQueue(arg);
      }
    }
    return result;
  }

  @Override
  public TraversalProcess visitQuantifier(
      BooleanFormula pF, Quantifier pQuantifier, List<Formula> boundVars, BooleanFormula pBody) {
    TraversalProcess result = delegate.visitQuantifier(pF, pQuantifier, boundVars, pBody);
    if (result == TraversalProcess.CONTINUE) {
      addToQueue(pBody);
    }
    return result;
  }
}
