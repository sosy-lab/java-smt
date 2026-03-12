// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Preconditions;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import org.sosy_lab.java_smt.api.FormulaType;

final class LeanSmtType {

  private enum Kind {
    BOOL,
    INT,
    REAL,
    BITVECTOR
  }

  static final LeanSmtType BOOL = new LeanSmtType(Kind.BOOL, 0);
  static final LeanSmtType INT = new LeanSmtType(Kind.INT, 0);
  static final LeanSmtType REAL = new LeanSmtType(Kind.REAL, 0);

  private static final Map<Integer, LeanSmtType> BITVECTOR_CACHE = new ConcurrentHashMap<>();

  private final Kind kind;
  private final int bitvectorSize;

  private LeanSmtType(Kind pKind, int pBitvectorSize) {
    kind = pKind;
    bitvectorSize = pBitvectorSize;
  }

  static LeanSmtType bitvector(int bitvectorSize) {
    Preconditions.checkArgument(bitvectorSize > 0, "Bitvector size must be positive");
    return BITVECTOR_CACHE.computeIfAbsent(bitvectorSize, size -> new LeanSmtType(Kind.BITVECTOR, size));
  }

  boolean isBool() {
    return kind == Kind.BOOL;
  }

  boolean isInt() {
    return kind == Kind.INT;
  }

  boolean isReal() {
    return kind == Kind.REAL;
  }

  boolean isBitvector() {
    return kind == Kind.BITVECTOR;
  }

  int getBitvectorSize() {
    Preconditions.checkState(isBitvector(), "Not a bitvector type: %s", this);
    return bitvectorSize;
  }

  FormulaType<?> toFormulaType() {
    switch (kind) {
      case BOOL:
        return FormulaType.BooleanType;
      case INT:
        return FormulaType.IntegerType;
      case REAL:
        return FormulaType.RationalType;
      case BITVECTOR:
        return FormulaType.getBitvectorTypeWithSize(bitvectorSize);
      default:
        throw new AssertionError("Unexpected LeanSMT type " + kind);
    }
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (!(other instanceof LeanSmtType)) {
      return false;
    }
    LeanSmtType that = (LeanSmtType) other;
    return kind == that.kind && bitvectorSize == that.bitvectorSize;
  }

  @Override
  public int hashCode() {
    return Objects.hash(kind, bitvectorSize);
  }

  @Override
  public String toString() {
    if (isBitvector()) {
      return "BV" + bitvectorSize;
    }
    return kind.name();
  }
}
