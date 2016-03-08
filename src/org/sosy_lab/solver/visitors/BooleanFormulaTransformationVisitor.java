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
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.List;

/**
 * Base class for visitors for boolean formulas that recursively transform
 * boolean formulas.
 *
 * @see BooleanFormulaManager#transformRecursively
 */
public abstract class BooleanFormulaTransformationVisitor
    implements BooleanFormulaVisitor<BooleanFormula> {

  private final BooleanFormulaManager bfmgr;

  protected BooleanFormulaTransformationVisitor(BooleanFormulaManager pBfmgr) {
    bfmgr = pBfmgr;
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
  public BooleanFormula visitNot(BooleanFormula pOperand) {
    return bfmgr.not(pOperand);
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> pOperands) {
    return bfmgr.and(pOperands);
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> pOperands) {
    return bfmgr.or(pOperands);
  }

  @Override
  public BooleanFormula visitXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.xor(operand1, operand2);
  }

  @Override
  public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.equivalence(pOperand1, pOperand2);
  }

  @Override
  public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.implication(pOperand1, pOperand2);
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return bfmgr.ifThenElse(pCondition, pThenFormula, pElseFormula);
  }

  @Override
  public BooleanFormula visitQuantifier(
      Quantifier quantifier,
      BooleanFormula quantifiedAST,
      List<Formula> boundVars,
      BooleanFormula body) {
    return quantifiedAST;
  }
}
