// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.errorprone.annotations.Immutable;
import org.checkerframework.checker.nullness.qual.Nullable;
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
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;

/**
 * A Formula represented as a TFormulaInfo object.
 *
 * @param <TFormulaInfo> the solver specific type.
 */
@Immutable(containerOf = "TFormulaInfo")
@SuppressWarnings("ClassTypeParameterName")
abstract class AbstractFormula<TFormulaInfo> implements Formula {

  private final TFormulaInfo formulaInfo;

  private AbstractFormula(TFormulaInfo formulaInfo) {
    this.formulaInfo = checkNotNull(formulaInfo);
  }

  @Override
  public final boolean equals(@Nullable Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof AbstractFormula)) {
      return false;
    }
    Object otherFormulaInfo = ((AbstractFormula<?>) o).formulaInfo;
    return formulaInfo == otherFormulaInfo || formulaInfo.equals(otherFormulaInfo);
  }

  final TFormulaInfo getFormulaInfo() {
    return formulaInfo;
  }

  @Override
  public final int hashCode() {
    return formulaInfo.hashCode();
  }

  @Override
  public final String toString() {
    return formulaInfo.toString();
  }

  /** Simple ArrayFormula implementation. */
  static final class ArrayFormulaImpl<TI extends Formula, TE extends Formula, TFormulaInfo>
      extends AbstractFormula<TFormulaInfo> implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    ArrayFormulaImpl(TFormulaInfo info, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
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

  /** Simple BooleanFormula implementation. Just tracing the size and the sign-treatment */
  static final class BitvectorFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements BitvectorFormula {
    BitvectorFormulaImpl(TFormulaInfo info) {
      super(info);
    }
  }

  /** Simple FloatingPointFormula implementation. */
  static final class FloatingPointFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements FloatingPointFormula {
    FloatingPointFormulaImpl(TFormulaInfo info) {
      super(info);
    }
  }

  /** Simple FloatingPointRoundingModeFormula implementation. */
  static final class FloatingPointRoundingModeFormulaImpl<TFormulaInfo>
      extends AbstractFormula<TFormulaInfo> implements FloatingPointRoundingModeFormula {
    FloatingPointRoundingModeFormulaImpl(TFormulaInfo info) {
      super(info);
    }
  }

  /** Simple BooleanFormula implementation. */
  static final class BooleanFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements BooleanFormula {
    BooleanFormulaImpl(TFormulaInfo pT) {
      super(pT);
    }
  }

  /** Simple IntegerFormula implementation. */
  static final class IntegerFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements IntegerFormula {
    IntegerFormulaImpl(TFormulaInfo pTerm) {
      super(pTerm);
    }
  }

  /** Simple RationalFormula implementation. */
  static final class RationalFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements RationalFormula {
    RationalFormulaImpl(TFormulaInfo pTerm) {
      super(pTerm);
    }
  }

  /** Simple StringFormula implementation. */
  static final class StringFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements StringFormula {
    StringFormulaImpl(TFormulaInfo pT) {
      super(pT);
    }
  }

  /** Simple RegexFormula implementation. */
  static final class RegexFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements RegexFormula {
    RegexFormulaImpl(TFormulaInfo pT) {
      super(pT);
    }
  }

  /** Simple EnumerationFormula implementation. */
  static final class EnumerationFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo>
      implements EnumerationFormula {
    EnumerationFormulaImpl(TFormulaInfo pT) {
      super(pT);
    }
  }
}
