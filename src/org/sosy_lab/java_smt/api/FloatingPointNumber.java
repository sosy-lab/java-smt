// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.auto.value.AutoValue;
import com.google.common.base.Preconditions;
import com.google.errorprone.annotations.Immutable;
import java.math.BigInteger;
import java.util.BitSet;

/**
 * Represents a floating-point number with customizable precision, consisting of sign, exponent, and
 * mantissa components.
 */
@Immutable
@AutoValue
public abstract class FloatingPointNumber {

  public static final int SINGLE_PRECISION_EXPONENT_SIZE = 8;
  public static final int SINGLE_PRECISION_MANTISSA_SIZE = 23;
  public static final int DOUBLE_PRECISION_EXPONENT_SIZE = 11;
  public static final int DOUBLE_PRECISION_MANTISSA_SIZE = 52;

  /** Whether the number is positive (TRUE) or negative (FALSE). */
  public abstract boolean getSign();

  /** The exponent of the floating-point number, given as numeric value. */
  public abstract BigInteger getExponent();

  /** The mantissa (aka significand) of the floating-point number, given as numeric value. */
  public abstract BigInteger getMantissa();

  public abstract int getExponentSize();

  public abstract int getMantissaSize();

  public static FloatingPointNumber of(
      boolean sign, BigInteger exponent, BigInteger mantissa, int exponentSize, int mantissaSize) {
    Preconditions.checkArgument(exponent.bitLength() <= exponentSize);
    Preconditions.checkArgument(mantissa.bitLength() <= mantissaSize);
    Preconditions.checkArgument(exponent.compareTo(BigInteger.ZERO) >= 0);
    Preconditions.checkArgument(mantissa.compareTo(BigInteger.ZERO) >= 0);
    return new AutoValue_FloatingPointNumber(sign, exponent, mantissa, exponentSize, mantissaSize);
  }

  public static FloatingPointNumber of(String bits, int exponentSize, int mantissaSize) {
    Preconditions.checkArgument(0 < exponentSize);
    Preconditions.checkArgument(0 < mantissaSize);
    Preconditions.checkArgument(
        bits.length() == 1 + exponentSize + mantissaSize,
        "Bitsize (%s) of floating point numeral does not match the size of sign, exponent and "
            + "mantissa (%s + %s + %s).",
        bits.length(),
        1,
        exponentSize,
        mantissaSize);
    Preconditions.checkArgument(bits.chars().allMatch(c -> c == '0' || c == '1'));
    boolean sign = bits.charAt(0) == '1';
    BigInteger exponent = new BigInteger(bits.substring(1, 1 + exponentSize), 2);
    BigInteger mantissa =
        new BigInteger(bits.substring(1 + exponentSize, 1 + exponentSize + mantissaSize), 2);
    return of(sign, exponent, mantissa, exponentSize, mantissaSize);
  }

  /**
   * Returns true if this floating-point number is an IEEE-754-2008 single precision type with 32
   * bits length consisting of an 8 bit exponent, a 23 bit mantissa and a single sign bit.
   *
   * @return true for IEEE-754 single precision type, false otherwise.
   */
  public boolean isIEEE754SinglePrecision() {
    return getExponentSize() == SINGLE_PRECISION_EXPONENT_SIZE
        && getMantissaSize() == SINGLE_PRECISION_MANTISSA_SIZE;
  }

  /**
   * Returns true if this floating-point number is an IEEE-754-2008 double precision type with 64
   * bits length consisting of an 11 bit exponent, a 52 bit mantissa and a single sign bit.
   *
   * @return true for IEEE-754 double precision type, false otherwise.
   */
  public boolean isIEEE754DoublePrecision() {
    return getExponentSize() == DOUBLE_PRECISION_EXPONENT_SIZE
        && getMantissaSize() == DOUBLE_PRECISION_MANTISSA_SIZE;
  }

  /** compute a representation as Java-based float value, if possible. */
  public float floatValue() {
    Preconditions.checkArgument(
        isIEEE754SinglePrecision(),
        "Can not represent floating point number %s as Java-based float value.",
        this);
    var bits = getBits();
    return Float.intBitsToFloat(bits.isEmpty() ? 0 : (int) bits.toLongArray()[0]);
  }

  /** compute a representation as Java-based double value, if possible. */
  public double doubleValue() {
    Preconditions.checkArgument(
        isIEEE754SinglePrecision() || isIEEE754DoublePrecision(),
        "Can not represent floating point number %s as Java-based double value.",
        this);
    if (isIEEE754SinglePrecision()) {
      // lets be nice to the user and automatically convert from single to double precision
      return floatValue();
    }
    var bits = getBits();
    return Double.longBitsToDouble(bits.isEmpty() ? 0 : getBits().toLongArray()[0]);
  }

  private BitSet getBits() {
    var mantissaSize = getMantissaSize();
    var exponentSize = getExponentSize();
    var mantissa = getMantissa();
    var exponent = getExponent();
    var bits = new BitSet(1 + exponentSize + mantissaSize);
    if (getSign()) {
      bits.set(exponentSize + mantissaSize);
    }
    for (int i = 0; i < exponentSize; i++) {
      bits.set(mantissaSize + i, exponent.testBit(i));
    }
    for (int i = 0; i < mantissaSize; i++) {
      bits.set(i, mantissa.testBit(i));
    }
    return bits;
  }

  /**
   * Return a bit-representation of sign-bit, exponent, and mantissa, i.e., a concatenation of their
   * bit-representations in this exact ordering.
   */
  @Override
  public final String toString() {
    var length = 1 + getExponentSize() + getMantissaSize();
    var str = new StringBuilder(length);
    var bits = getBits();
    for (int i = 0; i < length; i++) {
      str.append(bits.get(i) ? '1' : '0');
    }
    return str.reverse().toString();
  }
}
