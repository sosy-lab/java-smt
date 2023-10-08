// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

@Immutable
abstract class Mathsat5Formula implements Formula {

  private final long msatTerm;

  Mathsat5Formula(long term) {
    this.msatTerm = term;
  }

  @Override
  public final String toString() {
    return Mathsat5NativeApi.msat_term_repr(msatTerm);
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof Mathsat5Formula)) {
      return false;
    }
    return msatTerm == ((Mathsat5Formula) o).msatTerm;
  }

  @Override
  public final int hashCode() {
    return (int) msatTerm;
  }

  final long getTerm() {
    return msatTerm;
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class Mathsat5ArrayFormula<TI extends Formula, TE extends Formula>
      extends Mathsat5Formula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    Mathsat5ArrayFormula(long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
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
  static final class Mathsat5BitvectorFormula extends Mathsat5Formula implements BitvectorFormula {
    Mathsat5BitvectorFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Mathsat5FloatingPointFormula extends Mathsat5Formula
      implements FloatingPointFormula {
    Mathsat5FloatingPointFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Mathsat5FloatingPointRoundingModeFormula extends Mathsat5Formula
      implements FloatingPointRoundingModeFormula {
    Mathsat5FloatingPointRoundingModeFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Mathsat5IntegerFormula extends Mathsat5Formula implements IntegerFormula {
    Mathsat5IntegerFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Mathsat5RationalFormula extends Mathsat5Formula implements RationalFormula {
    Mathsat5RationalFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Mathsat5BooleanFormula extends Mathsat5Formula implements BooleanFormula {
    Mathsat5BooleanFormula(long pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Mathsat5EnumerationFormula extends Mathsat5Formula
      implements EnumerationFormula {
    Mathsat5EnumerationFormula(long pTerm) {
      super(pTerm);
    }
  }
}
