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
    return null;
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
  public boolean equivalence(Region f1, Region f2) {
    return f1.equals(f2);
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
  public boolean not(Region pBits) {
    return pBits.isFalse();

  }

  @Override
  public boolean and(Region pBits1, Region pBits2) {
    Region t;
    if (pBits1.isTrue() && pBits2.isTrue()) {
      return t.isTrue();
    } else {
      return t.isFalse();
    }

  }

  @Override
  public boolean or(Region pBits1, Region pBits2) {
    Region t;
    if (pBits1.isFalse() && pBits2.isFalse()) {
      return t.isFalse();
    } else {
      return t.isTrue();
    }
  }

  @Override
  public boolean xor(Region pBits1, Region pBits2) {
    Region t;
    if(pBits1.isTrue() && pBits2.isTrue() ) {
      return t.isFalse() ;
    } else if (pBits1.isFalse() && pBits2.isFalse()) {
      return t.isFalse();
    }
    else {
      t.isTrue();
    }
  }

}
