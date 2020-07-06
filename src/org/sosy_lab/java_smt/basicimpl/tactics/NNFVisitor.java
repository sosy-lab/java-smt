// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.tactics;

import com.google.common.collect.Lists;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;

public class NNFVisitor extends BooleanFormulaTransformationVisitor {
  private final NNFInsideNotVisitor insideNotVisitor;
  private final BooleanFormulaManager bfmgr;

  public NNFVisitor(FormulaManager pFmgr) {
    super(pFmgr);
    bfmgr = pFmgr.getBooleanFormulaManager();
    insideNotVisitor = new NNFInsideNotVisitor(pFmgr);
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula processedOperand) {
    return bfmgr.visit(processedOperand, insideNotVisitor);
  }

  @Override
  public BooleanFormula visitXor(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(rewriteXor(processedOperand1, processedOperand2), this);
  }

  private BooleanFormula rewriteXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.or(
        bfmgr.and(operand1, bfmgr.not(operand2)), bfmgr.and(bfmgr.not(operand1), operand2));
  }

  @Override
  public BooleanFormula visitEquivalence(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(rewriteEquivalence(processedOperand1, processedOperand2), this);
  }

  private BooleanFormula rewriteEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(
        bfmgr.and(pOperand1, pOperand2), bfmgr.and(bfmgr.not(pOperand1), bfmgr.not(pOperand2)));
  }

  @Override
  public BooleanFormula visitImplication(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(rewriteImplication(processedOperand1, processedOperand2), this);
  }

  private BooleanFormula rewriteImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(bfmgr.not(pOperand1), pOperand2);
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula processedCondition,
      BooleanFormula processedThenFormula,
      BooleanFormula processedElseFormula) {
    return bfmgr.visit(
        rewriteIfThenElse(processedCondition, processedThenFormula, processedElseFormula), this);
  }

  private BooleanFormula rewriteIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return bfmgr.or(
        bfmgr.and(pCondition, pThenFormula), bfmgr.and(bfmgr.not(pCondition), pElseFormula));
  }

  private class NNFInsideNotVisitor extends BooleanFormulaTransformationVisitor {

    protected NNFInsideNotVisitor(FormulaManager pFmgr) {
      super(pFmgr);
    }

    @Override
    public BooleanFormula visitConstant(boolean value) {
      return bfmgr.makeBoolean(value);
    }

    @Override
    public BooleanFormula visitAtom(
        BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
      return bfmgr.not(pAtom);
    }

    @Override
    public BooleanFormula visitNot(BooleanFormula processedOperand) {
      return bfmgr.visit(processedOperand, NNFVisitor.this);
    }

    @Override
    public BooleanFormula visitAnd(List<BooleanFormula> processedOperands) {
      return bfmgr.or(Lists.transform(processedOperands, f -> bfmgr.visit(f, this)));
    }

    @Override
    public BooleanFormula visitOr(List<BooleanFormula> processedOperands) {
      return bfmgr.and(Lists.transform(processedOperands, f -> bfmgr.visit(f, this)));
    }

    @Override
    public BooleanFormula visitXor(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
      return bfmgr.visit(rewriteXor(processedOperand1, processedOperand2), this);
    }

    @Override
    public BooleanFormula visitEquivalence(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
      return bfmgr.visit(rewriteEquivalence(processedOperand1, processedOperand2), this);
    }

    @Override
    public BooleanFormula visitImplication(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {

      // Rewrite using primitives.
      return bfmgr.visit(bfmgr.or(bfmgr.not(processedOperand1), processedOperand2), this);
    }

    @Override
    public BooleanFormula visitIfThenElse(
        BooleanFormula processedCondition,
        BooleanFormula processedThenFormula,
        BooleanFormula processedElseFormula) {
      return bfmgr.visit(
          rewriteIfThenElse(processedCondition, processedThenFormula, processedElseFormula), this);
    }
  }
}
