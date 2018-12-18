
package org.sosy_lab.java_smt.solvers.bdd;

import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;

abstract class BddFormula implements Formula {

  private final Region region;

  BddFormula(Region region) {
    this.region = region;
  }

  @Override
  public String toString() {
    return region.toString();
  }

  @Override
  public boolean equals(Object o) {
    if(o == this){
        return true;
    }
    if(!(o instanceof BddFormula)){
        return false;
    }
    return region == ((BddFormula) o).region;
    }

  @Override
  public int hashCode() {
    return this.region.hashCode();
  }

  final class BddBooleanFormula extends BddFormula implements BooleanFormula {
    BddBooleanFormula(Region pTerm) {
      super(pTerm);
    }

    public Region getRegion() {
      return region;
    }
  }
  static final class BddBitvectorFormula extends BddFormula implements BitvectorFormula {
    BddBitvectorFormula(Region pTerm) {
      super(pTerm);
    }
  }
}


/*
 * final class BddBooleanFormula extends BddFormula implements BooleanFormula {
 * BddBooleanFormula(Region pTerm) { super(pTerm); }
 *
 *
 * @Override public Region getFormulaInfo() { return region; } } /* static final class
 * BddBitvectorFormula extends BddFormula implements BitvectorFormula { BddBitvectorFormula(Region
 * pTerm) { super(pTerm); } } }
 *
 * static final class Mathsat5ArrayFormula<TI extends Formula, TE extends Formula> extends
 * Mathsat5Formula implements ArrayFormula<TI, TE> {
 *
 * private final FormulaType<TI> indexType; private final FormulaType<TE> elementType;
 *
 * Mathsat5ArrayFormula(Region pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
 * super(pTerm); indexType = pIndexType; elementType = pElementType; }
 *
 * public FormulaType<TI> getIndexType() { return indexType; }
 *
 * public FormulaType<TE> getElementType() { return elementType; } }
 *
 * static final class BddBitvectorFormula extends BddFormula implements BitvectorFormula {
 * BddBitvectorFormula(Region pTerm) { super(pTerm); } }
 */


