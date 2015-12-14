package org.sosy_lab.solver.basicimpl.tactics;

import com.google.common.collect.Maps;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.ArrayList;
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
      insideNot = false; // consume not
      return bfmgr.makeBoolean(false);
    } else {
      return bfmgr.makeBoolean(true);
    }
  }

  @Override
  public BooleanFormula visitFalse() {
    if (insideNot) {
      insideNot = false; // consume not
      return bfmgr.makeBoolean(true);
    } else {
      return bfmgr.makeBoolean(false);
    }
  }

  @Override
  public BooleanFormula visitAtom(BooleanFormula pAtom) {
    if (insideNot) {
      insideNot = false; // consume not
      return bfmgr.not(pAtom);
    } else {
      return pAtom;
    }
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula pOperand) {
    insideNot = !insideNot; // consume / set not
    return visit(pOperand);
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> pOperands) {
    boolean tmp = insideNot;
    List<BooleanFormula> newOperands = new ArrayList<>();
    for (BooleanFormula f : pOperands) {
      newOperands.add(visit(f));
      insideNot = tmp; // not is consumed in every iteration so we need to reset it
    }

    if (insideNot) {
      insideNot = false; // consume not
      return bfmgr.or(newOperands);
    } else {
      return bfmgr.and(newOperands);
    }
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> pOperands) {
    boolean tmp = insideNot;
    List<BooleanFormula> newOperands = new ArrayList<>();
    for (BooleanFormula f : pOperands) {
      newOperands.add(visit(f));
      insideNot = tmp; // not is consumed in every iteration so we need to reset it
    }

    if (insideNot) {
      insideNot = false; // consume not
      return bfmgr.and(newOperands);
    } else {
      return bfmgr.or(newOperands);
    }
  }

  @Override
  public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    boolean oldInsideNot = insideNot;
    insideNot = false; // consume not
    BooleanFormula p1 = visit(pOperand1);
    BooleanFormula p2 = visit(pOperand2);
    BooleanFormula p1Not = visit(bfmgr.not(pOperand1));
    BooleanFormula p2Not = visit(bfmgr.not(pOperand2));

    if (oldInsideNot) {
      return bfmgr.and(bfmgr.or(p1Not, p2Not), bfmgr.or(p1, p2));

    } else {
      return bfmgr.or(bfmgr.and(p1, p2), bfmgr.and(p1Not, p2Not));
    }
  }

  @Override
  public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    if (insideNot) {
      insideNot = false; // consume not
      BooleanFormula p1 = visit(pOperand1);
      BooleanFormula p2 = visit(bfmgr.not(pOperand2));
      return bfmgr.and(p1, p2);
    } else {
      BooleanFormula p1 = visit(bfmgr.not(pOperand1));
      BooleanFormula p2 = visit(pOperand2);
      return bfmgr.or(p1, p2);
    }
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    boolean oldInsideNot = insideNot;
    insideNot = false; // consume not
    BooleanFormula pC = visit(pCondition);
    BooleanFormula pCNot = visit(bfmgr.not(pCondition));

    if (oldInsideNot) {
      BooleanFormula pTNot = visit(bfmgr.not(pThenFormula));
      BooleanFormula pENot = visit(bfmgr.not(pElseFormula));
      return bfmgr.and(bfmgr.or(pCNot, pTNot), bfmgr.or(pC, pENot));

    } else {
      BooleanFormula pT = visit(pThenFormula);
      BooleanFormula pE = visit(pElseFormula);
      return bfmgr.or(bfmgr.and(pC, pT), bfmgr.and(pCNot, pE));
    }
  }
}
