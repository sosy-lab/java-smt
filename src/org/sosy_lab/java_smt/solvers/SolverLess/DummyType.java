/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package org.sosy_lab.java_smt.solvers.SolverLess;

import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;

public class DummyType {
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

  public DummyType(Type MyType) {
    if (MyType == Type.FLOATING_POINT || MyType == Type.ARRAY || MyType == Type.BITVECTOR
        || MyType == Type.FLOATINGPOINTROUNDINGMODE) {
      throw new UnsupportedOperationException(
          "Floating point, RoundModes, array types and Bitvectors need more "
              + "information");
    }
    this.myType = MyType;
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

  public String parseToSMTLIBFormulaType() {
    switch (this.myType) {
      case REGEX:
        return "Regex";
      case STRING:
        return "String";
      case FLOATING_POINT:
        return "(_ FloatingPoint ";
      case INTEGER:
        return "Int";
      case BITVECTOR:
        return "(_ BitVec ";
      case ARRAY:
        return "Array";
      case RATIONAL:
        return "Real";
      case BOOLEAN:
        return "Bool";
      case FLOATINGPOINTROUNDINGMODE:
        return roundingMode.giveSMTLIBFormat();
      default:
        throw new UnsupportedOperationException("Unsupported formula type");
    }
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
      return getRoundingMode().giveSMTLIBFormat();
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
}
