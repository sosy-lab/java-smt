package org.sosy_lab.java_smt.solvers.bdd;

import com.microsoft.z3.FuncDecl;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class BddBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Region, BddSort, RegionManager, FuncDecl>
{

  private final RegionManager rmgr;

  protected BddBooleanFormulaManager(
      FormulaCreator<Region, BddSort, RegionManager, FuncDecl> pCreator) {
    super(pCreator);
    this.rmgr = pCreator.getEnv();

  }

  @Override
  protected Region ifThenElse(Region pCond, Region pF1, Region pF2) {
    return rmgr.makeIte(pCond, pF1, pF2);
  }


  @Override
  public Region makeVariableImpl(String pVar) {
    BddSort booltype = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(booltype, pVar);
  }

  @Override
  public Region makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return rmgr.makeTrue();
    } else {
      return rmgr.makeFalse();
    }
  }

  @Override
  public Region equivalence(Region f1, Region f2) {
    return rmgr.makeEqual(f1, f2);
  }

  @Override
  public boolean isTrue(Region t) {
    return t.isTrue();
  }

  @Override
  public boolean isFalse(Region t) {
    return t.isFalse();
  }

  @Override
  public Region not(Region f) {
    return rmgr.makeNot(f);
  }

  @Override
  public Region and(Region pBits1, Region pBits2) {
    return rmgr.makeAnd(pBits1, pBits2);
  }

  @Override
  public Region or(Region pBits1, Region pBits2) {
    return rmgr.makeOr(pBits1, pBits2);
  }

  @Override
  public Region xor(Region pBits1, Region pBits2) {
    // return rmgr.makeNot(rmgr.makeEqual(pBits1, pBits2));
    return rmgr.makeUnequal(pBits1, pBits2);
  }

}
