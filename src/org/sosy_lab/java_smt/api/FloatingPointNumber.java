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
import com.google.errorprone.annotations.InlineMe;
import java.math.BigInteger;
import java.util.BitSet;

/**
 * Represents a floating-point number with customizable precision, consisting of sign, exponent, and
 * mantissa components.
 */
@Immutable
@AutoValue
public abstract class FloatingPointNumber {

  // Mantissas do not include the sign bit
  public static final int SINGLE_PRECISION_EXPONENT_SIZE = 8;
  public static final int SINGLE_PRECISION_MANTISSA_SIZE = 23;
  public static final int DOUBLE_PRECISION_EXPONENT_SIZE = 11;
  public static final int DOUBLE_PRECISION_MANTISSA_SIZE = 52;

  public enum Sign {
    POSITIVE,
    NEGATIVE;

    /**
     * get the Sign for a flag.
     *
     * @param isNegative whether the sign is negative (TRUE) or positive (FALSE).
     */
    public static Sign of(boolean isNegative) {
      return isNegative ? NEGATIVE : POSITIVE;
    }

    public boolean isNegative() {
      return this == NEGATIVE;
    }
  }

  /**
   * The sign of the floating-point number.
   *
   * @return whether the number is positive (FALSE) or negative (TRUE).
   */
  @Deprecated(
      since = "2025.01, because using a boolean flag as signBit is misleading",
      forRemoval = true)
  @InlineMe(
      replacement = "this.getMathSign() == Sign.NEGATIVE",
      imports = "org.sosy_lab.java_smt.api.FloatingPointNumber.Sign")
  public final boolean getSign() {
    return getMathSign() == Sign.NEGATIVE;
  }

  /** The sign of the floating-point number, i.e. whether it is positive or negative. */
  public abstract Sign getMathSign();

  /**
   * The exponent of the floating-point number, given as numeric value from binary representation.
   * The number is unsigned (not negative) and includes a bias of 2^(exponentSize-1)-1 that is used
   * in IEEE 754.
   */
  public abstract BigInteger getExponent();

  /**
   * The mantissa (aka significand) of the floating-point number, given as numeric value from binary
   * representation. The mantissa does not include the hidden bit that is used to denote normalized
   * numbers in IEEE 754.
   */
  public abstract BigInteger getMantissa();

  public abstract int getExponentSize();

  /**
   * Returns the size of the mantissa (also called a coefficient or significant), excluding the sign
   * bit.
   */
  // TODO: mark as soon to be deprecated
  public abstract int getMantissaSize();

  /**
   * Returns the size of the mantissa (also called a coefficient or significant), excluding the sign
   * bit.
   */
  public int getMantissaSizeWithoutSignBit() {
    return getMantissaSize();
  }

  /**
   * Returns the size of the mantissa (also called a coefficient or significant), including the sign
   * bit.
   */
  public int getMantissaSizeWithSignBit() {
    return getMantissaSize() + 1;
  }

  /**
   * Get a floating-point number with the given sign, exponent, and mantissa.
   *
   * @param sign the sign-bit of the floating-point number as specified by IEEE 754, aka FALSE for
   *     positive and TRUE for negative
   * @param exponent the exponent of the floating-point number, given as unsigned (not negative)
   *     number, including a bias of 2^(exponentSize-1)-1
   * @param mantissa the mantissa of the floating-point number, given as unsigned (not negative)
   *     number without hidden bit
   * @param exponentSize the (maximum) size of the exponent in bits
   * @param mantissaSize the (maximum) size of the mantissa in bits (excluding the sign bit)
   * @see #of(Sign, BigInteger, BigInteger, int, int)
   */
  @Deprecated(
      since = "2025.01, because using a boolean flag as signBit is misleading",
      forRemoval = true)
  @InlineMe(
      replacement =
          "FloatingPointNumber.of(Sign.of(sign), exponent, mantissa, exponentSize, mantissaSize)",
      imports = {
        "org.sosy_lab.java_smt.api.FloatingPointNumber",
        "org.sosy_lab.java_smt.api.FloatingPointNumber.Sign"
      })
  public static FloatingPointNumber of(
      boolean sign, BigInteger exponent, BigInteger mantissa, int exponentSize, int mantissaSize) {
    return of(Sign.of(sign), exponent, mantissa, exponentSize, mantissaSize);
  }

  /**
   * Get a floating-point number with the given sign, exponent, and mantissa.
   *
   * @param sign the sign of the floating-point number
   * @param exponent the exponent of the floating-point number, given as unsigned (not negative)
   *     number, including a bias of 2^(exponentSize-1)-1
   * @param mantissa the mantissa of the floating-point number, given as unsigned (not negative)
   *     number without hidden bit
   * @param exponentSize the (maximum) size of the exponent in bits
   * @param mantissaSize the (maximum) size of the mantissa in bits (excluding the sign bit)
   */
  public static FloatingPointNumber of(
      Sign sign, BigInteger exponent, BigInteger mantissa, int exponentSize, int mantissaSize) {
    Preconditions.checkArgument(exponent.bitLength() <= exponentSize);
    Preconditions.checkArgument(mantissa.bitLength() <= mantissaSize);
    Preconditions.checkArgument(exponent.compareTo(BigInteger.ZERO) >= 0);
    Preconditions.checkArgument(mantissa.compareTo(BigInteger.ZERO) >= 0);
    return new AutoValue_FloatingPointNumber(sign, exponent, mantissa, exponentSize, mantissaSize);
  }

  /**
   * Get a floating-point number encoded as bitvector as defined by IEEE 754.
   *
   * @param bits the bit-representation of the floating-point number, consisting of sign bit,
   *     exponent (without bias) and mantissa (without hidden bit) in this exact ordering
   * @param exponentSize the size of the exponent in bits
   * @param mantissaSize the size of the mantissa in bits (excluding the sign bit)
   */
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
    Sign sign = Sign.of(bits.charAt(0) == '1');
    BigInteger exponent = new BigInteger(bits.substring(1, 1 + exponentSize), 2);
    BigInteger mantissa =
        new BigInteger(bits.substring(1 + exponentSize, 1 + exponentSize + mantissaSize), 2);
    return of(sign, exponent, mantissa, exponentSize, mantissaSize);
  }

  /**
   * Returns true if this floating-point number is an IEEE-754-2008 single precision type with 32
   * bits length consisting of an 8 bit exponent, a 24 bit mantissa (including the sign bit).
   *
   * @return true for IEEE-754 single precision type, false otherwise.
   */
  public boolean isIEEE754SinglePrecision() {
    // Mantissa does not include the sign bit
    return getExponentSize() == SINGLE_PRECISION_EXPONENT_SIZE
        && getMantissaSizeWithoutSignBit() == SINGLE_PRECISION_MANTISSA_SIZE;
  }

  /**
   * Returns true if this floating-point number is an IEEE-754-2008 double precision type with 64
   * bits length consisting of an 11 bit exponent, a 53 bit mantissa (including the sign bit).
   *
   * @return true for IEEE-754 double precision type, false otherwise.
   */
  public boolean isIEEE754DoublePrecision() {
    // Mantissa does not include the sign bit
    return getExponentSize() == DOUBLE_PRECISION_EXPONENT_SIZE
        && getMantissaSizeWithoutSignBit() == DOUBLE_PRECISION_MANTISSA_SIZE;
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
      // let's be nice to the user and automatically convert from single to double precision
      return floatValue();
    }
    var bits = getBits();
    return Double.longBitsToDouble(bits.isEmpty() ? 0 : getBits().toLongArray()[0]);
  }

  private BitSet getBits() {
    var mantissaSizeWithoutSign = getMantissaSizeWithoutSignBit();
    var exponentSize = getExponentSize();
    var mantissa = getMantissa();
    var exponent = getExponent();
    var bits = new BitSet(exponentSize + mantissaSizeWithoutSign + 1);
    if (getMathSign().isNegative()) {
      bits.set(exponentSize + mantissaSizeWithoutSign); // if negative, set first bit to 1
    }
    for (int i = 0; i < exponentSize; i++) {
      bits.set(mantissaSizeWithoutSign + i, exponent.testBit(i));
    }
    for (int i = 0; i < mantissaSizeWithoutSign; i++) {
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
    var length = getExponentSize() + getMantissaSizeWithSignBit();
    var str = new StringBuilder(length);
    var bits = getBits();
    for (int i = 0; i < length; i++) {
      str.append(bits.get(i) ? '1' : '0');
    }
    return str.reverse().toString();
  }
}
