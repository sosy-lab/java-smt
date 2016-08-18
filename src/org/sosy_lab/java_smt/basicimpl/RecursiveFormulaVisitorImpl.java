/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.visitors.TraversalProcess;
import org.sosy_lab.java_smt.visitors.TraversalProcess.TraversalType;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

final class RecursiveFormulaVisitorImpl implements FormulaVisitor<TraversalProcess> {

  private final Set<Formula> seen = new HashSet<>();
  private final Deque<Formula> toVisit = new ArrayDeque<>();

  private final FormulaVisitor<TraversalProcess> delegate;

  RecursiveFormulaVisitorImpl(FormulaVisitor<TraversalProcess> pDelegate) {
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

  private void addToQueueIfNecessary(TraversalProcess result, List<? extends Formula> pOperands) {
    if (result == TraversalProcess.CONTINUE) {
      for (Formula f : pOperands) {
        addToQueue(f);
      }
    } else if (result.getType() == TraversalType.CUSTOM_TYPE) {
      pOperands.stream().filter(result::contains).forEach(this::addToQueue);
    }
  }

  Formula pop() {
    return toVisit.pop();
  }

  @Override
  public TraversalProcess visitFreeVariable(Formula pF, String pName) {
    return delegate.visitFreeVariable(pF, pName);
  }

  @Override
  public TraversalProcess visitBoundVariable(Formula pF, int pDeBruijnIdx) {
    return delegate.visitBoundVariable(pF, pDeBruijnIdx);
  }

  @Override
  public TraversalProcess visitConstant(Formula pF, Object pValue) {
    return delegate.visitConstant(pF, pValue);
  }

  @Override
  public TraversalProcess visitFunction(
      Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
    TraversalProcess result = delegate.visitFunction(pF, pArgs, pFunctionDeclaration);
    addToQueueIfNecessary(result, pArgs);
    return result;
  }

  @Override
  public TraversalProcess visitQuantifier(
      BooleanFormula pF, Quantifier pQuantifier, List<Formula> boundVars, BooleanFormula pBody) {
    TraversalProcess result = delegate.visitQuantifier(pF, pQuantifier, boundVars, pBody);
    addToQueueIfNecessary(result, ImmutableList.of(pBody));
    return result;
  }
}
