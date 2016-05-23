package org.sosy_lab.solver.basicimpl.tactics;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.ArrayList;
import java.util.List;

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
    return bfmgr.visit(insideNotVisitor, processedOperand);
  }

  @Override
  public BooleanFormula visitXor(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(this, rewriteXor(processedOperand1, processedOperand2));
  }

  private BooleanFormula rewriteXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.or(
        bfmgr.and(operand1, bfmgr.not(operand2)), bfmgr.and(bfmgr.not(operand1), operand2));
  }

  @Override
  public BooleanFormula visitEquivalence(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(this, rewriteEquivalence(processedOperand1, processedOperand2));
  }

  private BooleanFormula rewriteEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(
        bfmgr.and(pOperand1, pOperand2), bfmgr.and(bfmgr.not(pOperand1), bfmgr.not(pOperand2)));
  }

  @Override
  public BooleanFormula visitImplication(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(this, rewriteImplication(processedOperand1, processedOperand2));
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
        this, rewriteIfThenElse(processedCondition, processedThenFormula, processedElseFormula));
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
      return bfmgr.visit(NNFVisitor.this, processedOperand);
    }

    @Override
    public BooleanFormula visitAnd(List<BooleanFormula> processedOperands) {
      List<BooleanFormula> newOperands = new ArrayList<>();
      for (BooleanFormula f : processedOperands) {
        newOperands.add(bfmgr.visit(this, f));
      }

      return bfmgr.or(newOperands);
    }

    @Override
    public BooleanFormula visitOr(List<BooleanFormula> processedOperands) {
      List<BooleanFormula> newOperands = new ArrayList<>();
      for (BooleanFormula f : processedOperands) {
        newOperands.add(bfmgr.visit(this, f));
      }

      return bfmgr.and(newOperands);
    }

    @Override
    public BooleanFormula visitXor(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
      return bfmgr.visit(this, rewriteXor(processedOperand1, processedOperand2));
    }

    @Override
    public BooleanFormula visitEquivalence(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
      return bfmgr.visit(this, rewriteEquivalence(processedOperand1, processedOperand2));
    }

    @Override
    public BooleanFormula visitImplication(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {

      // Rewrite using primitives.
      return bfmgr.visit(this, bfmgr.or(bfmgr.not(processedOperand1), processedOperand2));
    }

    @Override
    public BooleanFormula visitIfThenElse(
        BooleanFormula processedCondition,
        BooleanFormula processedThenFormula,
        BooleanFormula processedElseFormula) {
      return bfmgr.visit(
          this, rewriteIfThenElse(processedCondition, processedThenFormula, processedElseFormula));
    }
  }
}
