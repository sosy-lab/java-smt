package org.sosy_lab.java_smt.solvers.bdd;
import net.sf.javabdd.BDD;

/**
 * Regions represented using BDDs from JavaBDD.
 */
class JavaBDDRegion implements Region {

  private final BDD bddRepr;

  JavaBDDRegion(BDD pBDD) {
    bddRepr = pBDD;
  }

  @Override
  public boolean isTrue() {
    return bddRepr.isOne();
  }

  @Override
  public boolean isFalse() {
    return bddRepr.isZero();
  }

  BDD getBDD() {
    return bddRepr;
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof JavaBDDRegion) {
      return bddRepr.equals(((JavaBDDRegion) o).bddRepr);
    }
    return false;
  }

  @Override
  public int hashCode() {
    return bddRepr.hashCode();
  }

  @Override
  public String toString() {
    if (bddRepr.isOne()) {
      return "true";
    } else if (bddRepr.isZero()) {
      return "false";
    } else {
      return bddRepr.toString();
    }
  }
}
