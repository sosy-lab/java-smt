// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.errorprone.annotations.Immutable;
import edu.stanford.CVC4.Expr;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;

@Immutable
public class CVC4Formula implements Formula {

  @SuppressWarnings("Immutable")
  private final Expr cvc4term;

  CVC4Formula(Expr term) {
    cvc4term = term;
  }

  @Override
  public final String toString() {
    return cvc4term.toString();
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof CVC4Formula)) {
      return false;
    }
    return cvc4term.equals(((CVC4Formula) o).cvc4term);
  }

  @Override
  public final int hashCode() {
    // termId works like a hashCode
    return cvc4term.getId().intValue();
  }

  final Expr getTerm() {
    return cvc4term;
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class CVC4ArrayFormula<TI extends Formula, TE extends Formula> extends CVC4Formula
      implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    CVC4ArrayFormula(Expr pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
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
  static final class CVC4BitvectorFormula extends CVC4Formula implements BitvectorFormula {
    CVC4BitvectorFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4FloatingPointFormula extends CVC4Formula implements FloatingPointFormula {
    CVC4FloatingPointFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4FloatingPointRoundingModeFormula extends CVC4Formula
      implements FloatingPointRoundingModeFormula {
    CVC4FloatingPointRoundingModeFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4IntegerFormula extends CVC4Formula implements IntegerFormula {
    CVC4IntegerFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4RationalFormula extends CVC4Formula implements RationalFormula {
    CVC4RationalFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4BooleanFormula extends CVC4Formula implements BooleanFormula {
    CVC4BooleanFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4StringFormula extends CVC4Formula implements StringFormula {
    CVC4StringFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC4RegexFormula extends CVC4Formula implements RegexFormula {
    CVC4RegexFormula(Expr pTerm) {
      super(pTerm);
    }
  }
}
