package org.sosy_lab.solver.basicimpl.tactics;

import com.google.common.collect.Maps;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

class NNFVisitor extends BooleanFormulaTransformationVisitor {
  private final NNFInsideNotVisitor insideNotVisitor;
  private final BooleanFormulaManager bfmgr;

  NNFVisitor(FormulaManager pFmgr) {
    super(pFmgr, Maps.<BooleanFormula, BooleanFormula>newHashMap());
    bfmgr = pFmgr.getBooleanFormulaManager();
    insideNotVisitor =
        new NNFInsideNotVisitor(pFmgr, new HashMap<BooleanFormula, BooleanFormula>());
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula pOperand) {
    return bfmgr.visit(insideNotVisitor, pOperand);
  }

  @Override
  public BooleanFormula visitXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.visit(this, rewriteXor(operand1, operand2));
  }

  private BooleanFormula rewriteXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.or(
        bfmgr.and(operand1, bfmgr.not(operand2)), bfmgr.and(bfmgr.not(operand1), operand2));
  }

  @Override
  public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.visit(this, rewriteEquivalence(pOperand1, pOperand2));
  }

  private BooleanFormula rewriteEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(
        bfmgr.and(pOperand1, pOperand2), bfmgr.and(bfmgr.not(pOperand1), bfmgr.not(pOperand2)));
  }

  @Override
  public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.visit(this, rewriteImplication(pOperand1, pOperand2));
  }

  private BooleanFormula rewriteImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(bfmgr.not(pOperand1), pOperand2);
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return bfmgr.visit(this, rewriteIfThenElse(pCondition, pThenFormula, pElseFormula));
  }

  private BooleanFormula rewriteIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return bfmgr.or(
        bfmgr.and(pCondition, pThenFormula), bfmgr.and(bfmgr.not(pCondition), pElseFormula));
  }

  private class NNFInsideNotVisitor extends BooleanFormulaTransformationVisitor {

    protected NNFInsideNotVisitor(
        FormulaManager pFmgr, Map<BooleanFormula, BooleanFormula> pCache) {
      super(pFmgr, pCache);
    }

    @Override
    public BooleanFormula visitTrue() {
      return bfmgr.makeBoolean(false);
    }

    @Override
    public BooleanFormula visitFalse() {
      return bfmgr.makeBoolean(true);
    }

    @Override
    public BooleanFormula visitAtom(BooleanFormula pAtom, FuncDecl decl) {
      return bfmgr.not(pAtom);
    }

    @Override
    public BooleanFormula visitNot(BooleanFormula pOperand) {
      return bfmgr.visit(NNFVisitor.this, pOperand);
    }

    @Override
    public BooleanFormula visitAnd(List<BooleanFormula> pOperands) {
      List<BooleanFormula> newOperands = new ArrayList<>();
      for (BooleanFormula f : pOperands) {
        newOperands.add(bfmgr.visit(this, f));
      }

      return bfmgr.or(newOperands);
    }

    @Override
    public BooleanFormula visitOr(List<BooleanFormula> pOperands) {
      List<BooleanFormula> newOperands = new ArrayList<>();
      for (BooleanFormula f : pOperands) {
        newOperands.add(bfmgr.visit(this, f));
      }

      return bfmgr.and(newOperands);
    }

    @Override
    public BooleanFormula visitXor(BooleanFormula pOperand1, BooleanFormula pOperand2) {
      return bfmgr.visit(this, rewriteXor(pOperand1, pOperand2));
    }

    @Override
    public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
      return bfmgr.visit(this, rewriteEquivalence(pOperand1, pOperand2));
    }

    @Override
    public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {

      // Rewrite using primitives.
      return bfmgr.visit(this, bfmgr.or(bfmgr.not(pOperand1), pOperand2));
    }

    @Override
    public BooleanFormula visitIfThenElse(
        BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
      return bfmgr.visit(this, rewriteIfThenElse(pCondition, pThenFormula, pElseFormula));
    }
  }
}
