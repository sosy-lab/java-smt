// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

abstract class DReal4Formula implements Formula {
  @SuppressWarnings("Immutable")
  private final DRealTerm<?, ?> term;

  DReal4Formula(DRealTerm<?, ?> pTerm) {
    this.term = pTerm;
  }

  final DRealTerm<?, ?> getTerm() {
    return term;
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    } else if (o instanceof DReal4Formula) {
      return term.equals(((DReal4Formula) o).getTerm());
    } else {
      return false;
    }
  }

  @Override
  public final String toString() {
    return term.toString();
  }

  @Override
  public final int hashCode() {
    return term.hashCode();
  }

  static final class DReal4BooleanFormula extends DReal4Formula implements BooleanFormula {
    DReal4BooleanFormula(DRealTerm<?, ?> pTerm) {
      super(pTerm);
    }
  }

  static final class DReal4RationalFormula extends DReal4Formula implements RationalFormula {
    DReal4RationalFormula(DRealTerm<?, ?> pTerm) {
      super(pTerm);
    }
  }

  static final class DReal4IntegerFormula extends DReal4Formula implements IntegerFormula {
    DReal4IntegerFormula(DRealTerm<?, ?> pTerm) {
      super(pTerm);
    }
  }
}
