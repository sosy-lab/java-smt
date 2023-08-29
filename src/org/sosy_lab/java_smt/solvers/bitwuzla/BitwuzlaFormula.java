package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.FormulaType;

@Immutable
abstract class BitwuzlaFormula implements Formula {
  private final long bitwuzlaTerm;

  BitwuzlaFormula(long term){
    bitwuzlaTerm = term;
  }
  final long getTerm() {
    return bitwuzlaTerm;
  }

  /**
   * returns an arbitrary representation of the formula, might be human- or machine-readable.
   *
   * <p>We do not guarantee that the returned String is in any way related to the formula. The
   * solver might apply escaping or even un-escaping. A user should not use the returned String for
   * further processing. For analyzing formulas, we recommend using a {@link FormulaVisitor}.
   */
  @Override
  public String toString() {
    return bitwuzlaJNI.bitwuzla_term_to_string(this.bitwuzlaTerm);
  }

  /**
   * checks whether the other object is a formula of the same structure. Does not apply an expensive
   * SAT-check to check equisatisfiability.
   *
   * <p>Two formulas that are structured in the same way, are determined as "equal". Due to
   * transformations and simplifications, two equisatisfiable formulas with different structure
   * might not be determined as "equal".
   */
  @Override
  public boolean equals(Object other) {
    if (other == this) {
      return true;
    }
    if (!(other instanceof BitwuzlaFormula)) {
      return false;
    }
    return bitwuzlaTerm == ((BitwuzlaFormula) other).getTerm();
  }

  /**
   * returns a valid hashCode satisfying the constraints given by {@link #equals}.
   */
  @Override
  public int hashCode() {
    // In this case, the long returned by the JNI is not a pointer, but the value itself.
    return (int) bitwuzlaJNI.bitwuzla_term_hash(bitwuzlaTerm);
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class BitwuzlaArrayFormula<TI extends Formula, TE extends Formula> extends BitwuzlaFormula
      implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    BitwuzlaArrayFormula(long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
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

  @Immutable
  static final class BitwuzlaBitvectorFormula extends BitwuzlaFormula implements BitvectorFormula {
    BitwuzlaBitvectorFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class BitwuzlaFloatingPointFormula extends BitwuzlaFormula implements FloatingPointFormula {
    BitwuzlaFloatingPointFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class BitwuzlaFloatingPointRoundingModeFormula extends BitwuzlaFormula
      implements FloatingPointRoundingModeFormula {
    BitwuzlaFloatingPointRoundingModeFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class BitwuzlaBooleanFormula extends BitwuzlaFormula implements BooleanFormula {
    BitwuzlaBooleanFormula(long pTerm) {
      super(pTerm);
    }
  }

}
