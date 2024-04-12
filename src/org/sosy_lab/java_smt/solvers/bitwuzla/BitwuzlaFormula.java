// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;

@Immutable
abstract class BitwuzlaFormula implements Formula {
  @SuppressWarnings("Immutable")
  private final Term bitwuzlaTerm;

  BitwuzlaFormula(final Term term) {
    bitwuzlaTerm = term;
  }

  final Term getTerm() {
    return bitwuzlaTerm;
  }

  @Override
  public String toString() {
    return bitwuzlaTerm.toString();
  }

  @Override
  public boolean equals(Object other) {
    if (other == this) {
      return true;
    }
    if (!(other instanceof BitwuzlaFormula)) {
      return false;
    }
    Term otherTerm = ((BitwuzlaFormula) other).getTerm();
    return bitwuzlaTerm.equals(otherTerm);
  }

  /** returns a valid hashCode satisfying the constraints given by {@link #equals}. */
  @Override
  public int hashCode() {
    return bitwuzlaTerm.hashCode();
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class BitwuzlaArrayFormula<TI extends Formula, TE extends Formula>
      extends BitwuzlaFormula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    BitwuzlaArrayFormula(Term pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
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
    BitwuzlaBitvectorFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class BitwuzlaFloatingPointFormula extends BitwuzlaFormula
      implements FloatingPointFormula {
    BitwuzlaFloatingPointFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class BitwuzlaFloatingPointRoundingModeFormula extends BitwuzlaFormula
      implements FloatingPointRoundingModeFormula {
    BitwuzlaFloatingPointRoundingModeFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class BitwuzlaBooleanFormula extends BitwuzlaFormula implements BooleanFormula {
    BitwuzlaBooleanFormula(Term pTerm) {
      super(pTerm);
    }
  }
}
