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
package org.sosy_lab.solver.visitors;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Base class for visitors for boolean formulas that traverse recursively
 * through the boolean part of the formula.
 * This class ensures that each identical subtree of the formula
 * is visited only once to avoid the exponential explosion.
 *
 * <p>
 * Subclasses of this class should call super.visit...() to ensure recursive
 * traversal. If such a call is omitted, the respective part of the formula
 * is not visited.
 * </p>
 *
 * <p>
 * No guarantee on iteration order is made.
 * </p>
 */
public abstract class RecursiveBooleanFormulaVisitor implements BooleanFormulaVisitor<Void> {

  private final BooleanFormulaManager bfmgr;
  private final Set<BooleanFormula> seen = new HashSet<>();

  protected RecursiveBooleanFormulaVisitor(FormulaManager pFmgr) {
    bfmgr = pFmgr.getBooleanFormulaManager();
  }

  private Void visitIfNotSeen(BooleanFormula f) {
    if (seen.add(f)) {
      return bfmgr.visit(this, f);
    }
    return null;
  }

  private Void visitMulti(List<BooleanFormula> pOperands) {
    for (BooleanFormula operand : pOperands) {
      visitIfNotSeen(operand);
    }
    return null;
  }

  @Override
  public Void visitNot(BooleanFormula pOperand) {
    return visitIfNotSeen(pOperand);
  }

  @Override
  public Void visitAnd(List<BooleanFormula> pOperands) {
    return visitMulti(pOperands);
  }

  @Override
  public Void visitOr(List<BooleanFormula> pOperands) {
    return visitMulti(pOperands);
  }

  @Override
  public Void visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    visitIfNotSeen(pOperand1);
    visitIfNotSeen(pOperand2);
    return null;
  }

  @Override
  public Void visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    visitIfNotSeen(pOperand1);
    visitIfNotSeen(pOperand2);
    return null;
  }

  @Override
  public Void visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    visitIfNotSeen(pCondition);
    visitIfNotSeen(pThenFormula);
    visitIfNotSeen(pElseFormula);
    return null;
  }

  @Override
  public Void visitQuantifier(Quantifier quantifier, BooleanFormula body) {
    return visitIfNotSeen(body);
  }
}
