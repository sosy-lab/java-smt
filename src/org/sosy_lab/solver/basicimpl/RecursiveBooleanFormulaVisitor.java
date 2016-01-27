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

import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

final class RecursiveBooleanFormulaVisitor implements BooleanFormulaVisitor<TraversalProcess> {

  private final Set<BooleanFormula> seen = new HashSet<>();
  private final Deque<BooleanFormula> toVisit = new ArrayDeque<>();

  private final BooleanFormulaVisitor<TraversalProcess> delegate;

  RecursiveBooleanFormulaVisitor(BooleanFormulaVisitor<TraversalProcess> pDelegate) {
    delegate = checkNotNull(pDelegate);
  }

  void addToQueue(BooleanFormula f) {
    if (seen.add(f)) {
      toVisit.push(f);
    }
  }

  boolean isQueueEmpty() {
    return toVisit.isEmpty();
  }

  BooleanFormula pop() {
    return toVisit.pop();
  }

  private void addToQueueIfNecessary(
      TraversalProcess result, BooleanFormula pOperand1, BooleanFormula pOperand2) {
    if (result == TraversalProcess.CONTINUE) {
      addToQueue(pOperand1);
      addToQueue(pOperand2);
    }
  }

  private void addToQueueIfNecessary(TraversalProcess result, List<BooleanFormula> pOperands) {
    if (result == TraversalProcess.CONTINUE) {
      for (BooleanFormula operand : pOperands) {
        addToQueue(operand);
      }
    }
  }

  @Override
  public TraversalProcess visitTrue() {
    return delegate.visitTrue();
  }

  @Override
  public TraversalProcess visitFalse() {
    return delegate.visitFalse();
  }

  @Override
  public TraversalProcess visitBoundVar(BooleanFormula var, int deBruijnIdx) {
    return delegate.visitBoundVar(var, deBruijnIdx);
  }

  @Override
  public TraversalProcess visitAtom(BooleanFormula pAtom, FunctionDeclaration decl) {
    return delegate.visitAtom(pAtom, decl);
  }

  @Override
  public TraversalProcess visitNot(BooleanFormula pOperand) {
    TraversalProcess result = delegate.visitNot(pOperand);
    if (result == TraversalProcess.CONTINUE) {
      addToQueue(pOperand);
    }
    return result;
  }

  @Override
  public TraversalProcess visitAnd(List<BooleanFormula> pOperands) {
    TraversalProcess result = delegate.visitAnd(pOperands);
    addToQueueIfNecessary(result, pOperands);
    return result;
  }

  @Override
  public TraversalProcess visitOr(List<BooleanFormula> pOperands) {
    TraversalProcess result = delegate.visitOr(pOperands);
    addToQueueIfNecessary(result, pOperands);
    return result;
  }

  @Override
  public TraversalProcess visitXor(BooleanFormula operand1, BooleanFormula operand2) {
    TraversalProcess result = delegate.visitXor(operand1, operand2);
    addToQueueIfNecessary(result, ImmutableList.of(operand1, operand2));
    return result;
  }

  @Override
  public TraversalProcess visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    TraversalProcess result = delegate.visitEquivalence(pOperand1, pOperand2);
    addToQueueIfNecessary(result, pOperand1, pOperand2);
    return result;
  }

  @Override
  public TraversalProcess visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    TraversalProcess result = delegate.visitImplication(pOperand1, pOperand2);
    addToQueueIfNecessary(result, pOperand1, pOperand2);
    return result;
  }

  @Override
  public TraversalProcess visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    TraversalProcess result = delegate.visitIfThenElse(pCondition, pThenFormula, pElseFormula);
    if (result == TraversalProcess.CONTINUE) {
      addToQueue(pCondition);
      addToQueue(pThenFormula);
      addToQueue(pElseFormula);
    }
    return result;
  }

  @Override
  public TraversalProcess visitQuantifier(
      Quantifier pQuantifier, List<Formula> boundVars, BooleanFormula pBody) {
    TraversalProcess result = delegate.visitQuantifier(pQuantifier, boundVars, pBody);
    if (result == TraversalProcess.CONTINUE) {
      addToQueue(pBody);
    }
    return result;
  }
}
