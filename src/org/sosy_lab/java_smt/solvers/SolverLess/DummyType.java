// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;

@SuppressWarnings({"all", "overrides"})
public class DummyType {
  /** This class ensures Type-safety for DummyFormulas. */
  private int bitvectorLength;

  private int exponent;
  private int mantissa;
  private Type arrayIndexType;
  private Type arrayElementType;
  public Type myType;
  public FloatingPointRoundingMode roundingMode;

  public DummyType(int bitvectorLength) {
    this.bitvectorLength = bitvectorLength;
    this.myType = Type.BITVECTOR;
  }

  public DummyType(Type pType) {
    if (pType == Type.FLOATING_POINT
        || pType == Type.ARRAY
        || pType == Type.BITVECTOR
        || pType == Type.FLOATINGPOINTROUNDINGMODE) {
      throw new UnsupportedOperationException(
          "Floating point, RoundModes, array types and Bitvectors need more " + "information");
    }
    this.myType = pType;
  }

  public DummyType(FloatingPointRoundingMode roundingMode) {
    this.roundingMode = roundingMode;
    this.myType = Type.FLOATINGPOINTROUNDINGMODE;
  }

  public DummyType(int exponent, int mantissa) {
    this.exponent = exponent;
    this.mantissa = mantissa;
    this.roundingMode = FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;
    this.myType = Type.FLOATING_POINT;
  }

  public DummyType(int exponent, int mantissa, FloatingPointRoundingMode roundingMode) {
    this.exponent = exponent;
    this.mantissa = mantissa;
    this.roundingMode = roundingMode;
    this.myType = Type.FLOATING_POINT;
  }

  public DummyType(Type indexType, Type elementType) {
    this.myType = Type.ARRAY;
    this.arrayIndexType = indexType;
    this.arrayElementType = elementType;
  }

  public enum Type {
    REGEX,
    STRING,
    FLOATING_POINT,
    INTEGER,
    BITVECTOR,
    ARRAY,
    RATIONAL,
    BOOLEAN,
    FLOATINGPOINTROUNDINGMODE
  }

  public boolean isFloatingPoint() {
    return myType == Type.FLOATING_POINT;
  }

  public boolean isBitvector() {
    return myType == Type.BITVECTOR;
  }

  public boolean isInteger() {
    return myType == Type.INTEGER;
  }

  public boolean isRational() {
    return myType == Type.RATIONAL;
  }

  public boolean isBoolean() {
    return myType == Type.BOOLEAN;
  }

  public boolean isString() {
    return myType == Type.STRING;
  }

  public boolean isRegex() {
    return myType == Type.REGEX;
  }

  public boolean isArray() {
    return myType == Type.ARRAY;
  }

  public boolean isFloatingPointRoundingMode() {
    return myType == Type.FLOATINGPOINTROUNDINGMODE;
  }

  public int getBitvectorLength() {
    if (myType != Type.BITVECTOR) {
      throw new UnsupportedOperationException("Not a bitvector type");
    }
    return bitvectorLength;
  }

  public int getExponent() {
    if (myType != Type.FLOATING_POINT) {
      throw new UnsupportedOperationException("Not a floating point type");
    }
    return exponent;
  }

  public int getMantissa() {
    if (myType != Type.FLOATING_POINT) {
      throw new UnsupportedOperationException("Not a floating point type");
    }
    return mantissa;
  }

  public FloatingPointRoundingMode getRoundingMode() {
    if (myType != Type.FLOATINGPOINTROUNDINGMODE && myType != Type.FLOATING_POINT) {
      throw new UnsupportedOperationException("Not a floating point rounding mode type");
    }
    return roundingMode;
  }

  public Type getArrayIndexType() {
    if (myType != Type.ARRAY) {
      throw new UnsupportedOperationException("Not an array type");
    }
    return arrayIndexType;
  }

  public Type getArrayElementType() {
    if (myType != Type.ARRAY) {
      throw new UnsupportedOperationException("Not an array type");
    }
    return arrayElementType;
  }

  @Override
  public String toString() {
    if (isFloatingPoint()) {
      return "FloatingPoint<" + getExponent() + ", " + getMantissa() + ">";
    }
    if (isBitvector()) {
      return "Bitvector<" + getBitvectorLength() + ">";
    }
    if (isArray()) {
      return "Array<" + getArrayIndexType() + ", " + getArrayElementType() + ">";
    }
    if (isFloatingPointRoundingMode()) {
      return getRoundingMode().getSMTLIBFormat();
    }

    return myType.toString();
  }

  @Override
  public boolean equals(Object other) {
    if (other == this) {
      return true;
    }
    if (other instanceof DummyType) {
      DummyType otherType = (DummyType) other;
      if (otherType.myType == this.myType) {
        if (this.myType == Type.BITVECTOR) {
          return otherType.bitvectorLength == this.bitvectorLength;
        }
        if (this.myType == Type.FLOATINGPOINTROUNDINGMODE) {
          return otherType.roundingMode == this.roundingMode;
        }
        if (this.myType == Type.FLOATING_POINT) {
          return otherType.exponent == this.exponent && otherType.mantissa == this.mantissa;
        }
        if (this.myType == Type.ARRAY) {
          return otherType.arrayIndexType == this.arrayIndexType
              && otherType.arrayElementType == this.arrayElementType;
        }
        return true;
      }
    }
    return false;
  }

  @Override
  public int hashCode() {
    int result = myType.hashCode();
    switch (myType) {
      case BITVECTOR:
        result = 31 * result + bitvectorLength;
        break;
      case FLOATINGPOINTROUNDINGMODE:
        result = 31 * result + (roundingMode != null ? roundingMode.hashCode() : 0);
        break;
      case FLOATING_POINT:
        result = 31 * result + exponent;
        result = 31 * result + mantissa;
        break;
      case ARRAY:
        result = 31 * result + (arrayIndexType != null ? arrayIndexType.hashCode() : 0);
        result = 31 * result + (arrayElementType != null ? arrayElementType.hashCode() : 0);
        break;
      default:
        break;
    }
    return result;
  }
}
