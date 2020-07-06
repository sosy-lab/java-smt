// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@Immutable
abstract class BoolectorFormula implements Formula {

  private final long btorTerm;
  private final long btor; // We need the boolector instance to calculate the hash

  BoolectorFormula(long term, long btor) {
    this.btorTerm = term;
    this.btor = btor;
  }

  final long getTerm() {
    return btorTerm;
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof BoolectorFormula)) {
      return false;
    }
    BoolectorFormula other = (BoolectorFormula) o;
    return btor == other.btor && btorTerm == other.btorTerm;
  }

  @Override
  public final int hashCode() {
    // Boolector uses structural hashing on its nodes (formulas)
    return BtorJNI.boolector_get_node_id(btor, btorTerm);
  }

  @Immutable
  static final class BoolectorBitvectorFormula extends BoolectorFormula
      implements BitvectorFormula {
    BoolectorBitvectorFormula(long pTerm, long btor) {
      super(pTerm, btor);
    }
  }

  @Immutable
  static final class BoolectorBooleanFormula extends BoolectorFormula implements BooleanFormula {
    BoolectorBooleanFormula(long pTerm, long btor) {
      super(pTerm, btor);
    }
  }

  @SuppressWarnings("ClassTypeParameterName")
  static final class BoolectorArrayFormula<TI extends Formula, TE extends Formula>
      extends BoolectorFormula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    BoolectorArrayFormula(
        long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType, long btor) {
      super(pTerm, btor);
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
}
