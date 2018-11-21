
package org.sosy_lab.java_smt.solvers.bdd;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

abstract class BddFormula implements Formula {

  private final Region region;
 

  BddFormula(Region region {
    this.region = region;
  }

  @Override
  public final String toString(){
  return Mathsat5NativeApi.msat_term_repr(region);
  }
  
  @Override
  public final boolean equals(Object o){
    if(o == this){
        return true;
    }
    if(!(o instanceof BddFormula)){
        return false;
    }
    return region == ((BddFormula) o).region;
    }
    
  @Override
  public final int hashCode() {
    return (int) region;
  }


  final long getRegion() {
    return region;
  }

  /*static final class Mathsat5ArrayFormula<TI extends Formula, TE extends Formula>
      extends Mathsat5Formula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    Mathsat5ArrayFormula(Region pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(pTerm);
      indexType = pIndexType;
      elementType = pElementType;
    }

    public FormulaType<TI> getIndexType() {
      return indexType;
    }

    public FormulaType<TE> getElementType() {
      return elementType;
    }
  }

  static final class BddBitvectorFormula extends BddFormula implements BitvectorFormula {
    BddBitvectorFormula(Region pTerm) {
      super(pTerm);
    }
  }

  static final class Bdd5BooleanFormula extends BddFormula implements BooleanFormula {
    BddBooleanFormula(Region pTerm) {
      super(pTerm);
    }
  }
}
*/
  
