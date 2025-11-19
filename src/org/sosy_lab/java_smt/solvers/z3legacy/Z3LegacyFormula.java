/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.errorprone.annotations.Immutable;
import com.microsoft.z3legacy.Native;
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

@Immutable
abstract class Z3LegacyFormula implements Formula {

  private final long z3expr;
  private final long z3context;
  private final int hashCache;

  private Z3LegacyFormula(long z3context, long z3expr) {
    checkArgument(z3context != 0, "Z3 context is null");
    checkArgument(z3expr != 0, "Z3 formula is null");
    this.z3expr = z3expr;
    this.z3context = z3context;

    Native.incRef(z3context, z3expr);
    this.hashCache = Native.getAstHash(z3context, z3expr);
  }

  @Override
  public final String toString() {
    return Native.astToString(z3context, z3expr);
  }

  @Override
  public final boolean equals(@Nullable Object obj) {
    if (obj == this) {
      return true;
    }
    if (!(obj instanceof Z3LegacyFormula)) {
      return false;
    }
    Z3LegacyFormula other = (Z3LegacyFormula) obj;
    return (z3context == other.z3context) && Native.isEqAst(z3context, z3expr, other.z3expr);
  }

  @Override
  public final int hashCode() {
    return hashCache;
  }

  final long getFormulaInfo() {
    return z3expr;
  }

  @SuppressWarnings("ClassTypeParameterName")
  static final class Z3ArrayLegacyFormula<TI extends Formula, TE extends Formula>
      extends Z3LegacyFormula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    Z3ArrayLegacyFormula(
        long pZ3context, long pZ3expr, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(pZ3context, pZ3expr);
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
  static final class Z3BitvectorLegacyFormula extends Z3LegacyFormula implements BitvectorFormula {

    Z3BitvectorLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3FloatingPointLegacyFormula extends Z3LegacyFormula
      implements FloatingPointFormula {

    Z3FloatingPointLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3FloatingPointRoundingModeLegacyFormula extends Z3LegacyFormula
      implements FloatingPointRoundingModeFormula {

    Z3FloatingPointRoundingModeLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3IntegerLegacyFormula extends Z3LegacyFormula implements IntegerFormula {

    Z3IntegerLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3RationalLegacyFormula extends Z3LegacyFormula implements RationalFormula {

    Z3RationalLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3BooleanLegacyFormula extends Z3LegacyFormula implements BooleanFormula {
    Z3BooleanLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3StringLegacyFormula extends Z3LegacyFormula implements StringFormula {
    Z3StringLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3RegexLegacyFormula extends Z3LegacyFormula implements RegexFormula {
    Z3RegexLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3EnumerationLegacyFormula extends Z3LegacyFormula
      implements EnumerationFormula {
    Z3EnumerationLegacyFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }
}
