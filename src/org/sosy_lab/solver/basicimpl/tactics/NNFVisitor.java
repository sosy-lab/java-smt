package org.sosy_lab.solver.basicimpl.tactics;

import com.google.common.collect.Maps;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.List;

class NNFVisitor extends BooleanFormulaTransformationVisitor {
  boolean insideNot = false;

  private final BooleanFormulaManager bfmgr;

  NNFVisitor(FormulaManager pFmgr) {
    super(pFmgr, Maps.<BooleanFormula, BooleanFormula>newHashMap());
    bfmgr = pFmgr.getBooleanFormulaManager();
  }

  @Override
  public BooleanFormula visitTrue() {
    if (insideNot) {
      return bfmgr.makeBoolean(false);
    } else {
      return bfmgr.makeBoolean(true);
    }
  }

  @Override
  public BooleanFormula visitFalse() {
    if (insideNot) {
      return bfmgr.makeBoolean(true);
    } else {
      return bfmgr.makeBoolean(false);
    }
  }

  @Override
  public BooleanFormula visitAtom(BooleanFormula pAtom) {
    if (insideNot) {
      return bfmgr.not(pAtom);
    } else {
      return pAtom;
    }
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula pOperand) {
    boolean savedState = insideNot;
    insideNot = !insideNot;
    BooleanFormula out = visitIfNotSeen(visitIfNotSeen(pOperand));

    // Restore the state on leaving the traversal.
    insideNot = savedState;
    return out;
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> pOperands) {
    if (insideNot) {
      return bfmgr.or(visitIfNotSeen(pOperands));
    } else {
      return bfmgr.and(visitIfNotSeen(pOperands));
    }
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> pOperands) {
    if (insideNot) {
      return bfmgr.and(visitIfNotSeen(pOperands));
    } else {
      return bfmgr.or(visitIfNotSeen(pOperands));
    }
  }

  @Override
  public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    if (insideNot) {
      BooleanFormula p1 = visitIfNotSeen(pOperand1);
      BooleanFormula p2 = visitIfNotSeen(pOperand2);
      return bfmgr.or(
          bfmgr.and(p1, bfmgr.not(p2)),
          bfmgr.and(bfmgr.not(p1), p2));
    } else {
      return super.visitEquivalence(pOperand1, pOperand2);
    }
  }

  @Override
  public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    if (insideNot) {
      BooleanFormula p1 = visitIfNotSeen(pOperand1);
      BooleanFormula p2 = visitIfNotSeen(pOperand2);
      return bfmgr.and(p1, bfmgr.not(p2));
    } else {
      return super.visitImplication(pOperand1, pOperand2);
    }
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    if (insideNot) {
      BooleanFormula pC = visitIfNotSeen(pCondition);
      BooleanFormula pT = visitIfNotSeen(pThenFormula);
      BooleanFormula pE = visitIfNotSeen(pElseFormula);
      return bfmgr.and(
          bfmgr.or(bfmgr.not(pC), bfmgr.not(pT)),
          bfmgr.or(pC, pE)
      );
    } else {
      return super.visitIfThenElse(pCondition, pThenFormula, pElseFormula);
    }
  }
}
