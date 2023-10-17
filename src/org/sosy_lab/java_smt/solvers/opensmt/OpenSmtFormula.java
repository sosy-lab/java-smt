// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.errorprone.annotations.Immutable;
import java.util.Objects;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;

@Immutable
public class OpenSmtFormula implements Formula {

  @SuppressWarnings("Immutable")
  private final Logic osmtLogic;

  @SuppressWarnings("Immutable")
  private final PTRef osmtTerm;

  OpenSmtFormula(Logic logic, PTRef term) {
    osmtLogic = logic;
    osmtTerm = term;
  }

  @Override
  public final String toString() {
    return osmtLogic.pp(osmtTerm);
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof OpenSmtFormula)) {
      return false;
    }
    OpenSmtFormula that = (OpenSmtFormula) o;
    return this.osmtLogic.equals(that.osmtLogic) && this.osmtTerm.equals(that.osmtTerm);
  }

  @Override
  public final int hashCode() {
    return Objects.hash(osmtLogic, osmtTerm);
  }

  final PTRef getOsmtTerm() {
    return osmtTerm;
  }

  @Immutable
  @SuppressWarnings("ClassTypeParameterName")
  static final class OpenSmtArrayFormula<TI extends Formula, TE extends Formula>
      extends OpenSmtFormula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    OpenSmtArrayFormula(
        Logic pLogic, PTRef pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(pLogic, pTerm);
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
  static final class OpenSmtIntegerFormula extends OpenSmtFormula implements IntegerFormula {
    OpenSmtIntegerFormula(Logic pLogic, PTRef pTerm) {
      super(pLogic, pTerm);
    }
  }

  @Immutable
  static final class OpenSmtRationalFormula extends OpenSmtFormula implements RationalFormula {
    OpenSmtRationalFormula(Logic pLogic, PTRef pTerm) {
      super(pLogic, pTerm);
    }
  }

  @Immutable
  static final class OpenSmtBooleanFormula extends OpenSmtFormula implements BooleanFormula {
    OpenSmtBooleanFormula(Logic pLogic, PTRef pTerm) {
      super(pLogic, pTerm);
    }
  }
}
