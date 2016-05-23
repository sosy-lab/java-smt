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

import com.google.common.collect.Collections2;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.Collection;
import java.util.List;

/**
 * Base class for visitors for boolean formulas that recursively transform
 * boolean formulas.
 *
 * @see BooleanFormulaManager#transformRecursively
 */
public abstract class BooleanFormulaTransformationVisitor
    implements BooleanFormulaVisitor<BooleanFormula> {

  private final FormulaManager mgr;
  private final BooleanFormulaManager bfmgr;

  protected BooleanFormulaTransformationVisitor(FormulaManager pMgr) {
    mgr = pMgr;
    bfmgr = mgr.getBooleanFormulaManager();
  }

  @Override
  public BooleanFormula visitConstant(boolean value) {
    return bfmgr.makeBoolean(value);
  }

  @Override
  public BooleanFormula visitBoundVar(BooleanFormula var, int deBruijnIdx) {
    return var;
  }

  @Override
  public BooleanFormula visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
    return pAtom;
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula processedOperand) {
    return bfmgr.not(processedOperand);
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> processedOperands) {
    for (BooleanFormula op : processedOperands) {
      if (bfmgr.isFalse(op)) {
        return bfmgr.makeBoolean(false);
      }
    }

    // Filtered collections avoid extra allocations.
    Collection<BooleanFormula> filtered =
        Collections2.filter(processedOperands, input -> !bfmgr.isTrue(input));
    return bfmgr.and(filtered);
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> processedOperands) {
    for (BooleanFormula op : processedOperands) {
      if (bfmgr.isTrue(op)) {
        return bfmgr.makeBoolean(true);
      }
    }
    Collection<BooleanFormula> filtered =
        Collections2.filter(processedOperands, input -> !bfmgr.isFalse(input));
    return bfmgr.or(filtered);
  }

  @Override
  public BooleanFormula visitXor(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.xor(processedOperand1, processedOperand2);
  }

  @Override
  public BooleanFormula visitEquivalence(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.equivalence(processedOperand1, processedOperand2);
  }

  @Override
  public BooleanFormula visitImplication(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.implication(processedOperand1, processedOperand2);
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula processedCondition,
      BooleanFormula processedThenFormula,
      BooleanFormula processedElseFormula) {
    return bfmgr.ifThenElse(processedCondition, processedThenFormula, processedElseFormula);
  }

  @Override
  public BooleanFormula visitQuantifier(
      Quantifier quantifier,
      BooleanFormula quantifiedAST,
      List<Formula> boundVars,
      BooleanFormula processedBody) {
    return mgr.getQuantifiedFormulaManager().mkQuantifier(quantifier, boundVars, processedBody);
  }
}
