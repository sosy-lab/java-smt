package org.sosy_lab.java_smt.solvers.bdd;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class BddBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Region, Sort, Context, funcDecl>
{

  private final Region region;

  // TODO
  protected BddBooleanFormulaManager(BddFormulaManager pCreator) {
    super(pCreator);
    this.region = pCreator.getEnv();

  }

  // TODO
  @Override
  public Region makeVariableImpl(String pVar) {
    // long boolType = getFormulaCreator().getBoolType();
    // return getFormulaCreator().makeVariable(boolType, pVar);
    // long boolType = getFormulaCreator().getBoolType();
    return formulaCreator.makeVariable(formulaCreator.getBoolType(), pVar);
  }

  @Override
  public Region makeBooleanImpl(Boolean pValue) {
    Region t;
    if (pValue) {
      t.isTrue();
    } else {
      t.isFalse();
    }
    return t;
  }

  @Override
  public Region equivalence(Region f1, Region f2) {
      f1.equals(f2);
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
  public Region not(Region pBits) {
    Region param1 = extractInfo(pBits);

    return (not(pBits));
  }

  @Override
  public Region and(Region pBits1, Region pBits2) {
    Region param1 = extractInfo(pBits1);
    Region param2 = extractInfo(pBits2);

    return (and(param1, param2));
  }

  @Override
  public Region or(Region pBits1, Region pBits2) {
    Region param1 = extractInfo(pBits1);
    Region param2 = extractInfo(pBits2);

    return (or(param1, param2));
  }

  @Override
  public Region xor(Region pBits1, Region pBits2) {
    Region param1 = extractInfo(pBits1);
    Region param2 = extractInfo(pBits2);

    return (xor(param1, param2));
  }
}
