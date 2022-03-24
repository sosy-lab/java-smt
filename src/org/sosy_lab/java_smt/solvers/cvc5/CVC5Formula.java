// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.errorprone.annotations.Immutable;
import io.github.cvc5.api.Term;
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
public class CVC5Formula implements Formula {

  @SuppressWarnings("Immutable")
  private final Term cvc5term;

  CVC5Formula(Term term) {
    cvc5term = term;
  }

  @Override
  public final String toString() {
    return cvc5term.toString();
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof CVC5Formula)) {
      return false;
    }
    return cvc5term.equals(((CVC5Formula) o).cvc5term);
  }

  @Override
  public final int hashCode() {
    return Long.hashCode(cvc5term.getId());
  }

  final Term getTerm() {
    return cvc5term;
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class CVC5ArrayFormula<TI extends Formula, TE extends Formula> extends CVC5Formula
      implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    CVC5ArrayFormula(Term pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
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
  static final class CVC5BitvectorFormula extends CVC5Formula implements BitvectorFormula {
    CVC5BitvectorFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5FloatingPointFormula extends CVC5Formula implements FloatingPointFormula {
    CVC5FloatingPointFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5FloatingPointRoundingModeFormula extends CVC5Formula
      implements FloatingPointRoundingModeFormula {
    CVC5FloatingPointRoundingModeFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5IntegerFormula extends CVC5Formula implements IntegerFormula {
    CVC5IntegerFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5RationalFormula extends CVC5Formula implements RationalFormula {
    CVC5RationalFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5BooleanFormula extends CVC5Formula implements BooleanFormula {
    CVC5BooleanFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5StringFormula extends CVC5Formula implements StringFormula {
    CVC5StringFormula(Term pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class CVC5RegexFormula extends CVC5Formula implements RegexFormula {
    CVC5RegexFormula(Term pTerm) {
      super(pTerm);
    }
  }
}
