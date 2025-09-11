// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

@Immutable
abstract class Yices2Formula implements Formula {

  private final int yicesTerm;

  Yices2Formula(int term) {
    this.yicesTerm = term;
  }

  @Override
  public final int hashCode() {
    return yicesTerm;
  }

  final int getTerm() {
    return yicesTerm;
  }

  @Override
  public final String toString() {
    return yices_term_to_string(yicesTerm);
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof Yices2Formula)) {
      return false;
    }
    return yicesTerm == ((Yices2Formula) o).yicesTerm;
  }

  @Immutable
  static final class Yices2BitvectorFormula extends Yices2Formula implements BitvectorFormula {
    Yices2BitvectorFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2IntegerFormula extends Yices2Formula implements IntegerFormula {
    Yices2IntegerFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2RationalFormula extends Yices2Formula implements RationalFormula {
    Yices2RationalFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2BooleanFormula extends Yices2Formula implements BooleanFormula {
    Yices2BooleanFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2ArrayFormula<TI extends Formula, TE extends Formula>
      extends Yices2Formula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    Yices2ArrayFormula(Integer info, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(info);
      this.indexType = checkNotNull(pIndexType);
      this.elementType = checkNotNull(pElementType);
    }

    public FormulaType<TI> getIndexType() {
      return indexType;
    }

    public FormulaType<TE> getElementType() {
      return elementType;
    }
  }
}
