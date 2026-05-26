// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api.visitors;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;

/**
 * Base class for visitors for boolean formulas that recursively transform boolean formulas.
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
  public BooleanFormula visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
    return pAtom;
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula processedOperand) {
    return bfmgr.not(processedOperand);
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> processedOperands) {
    return bfmgr.and(processedOperands);
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> processedOperands) {
    return bfmgr.or(processedOperands);
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
