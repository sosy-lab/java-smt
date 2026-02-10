// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.api.FormulaType.getFloatingPointTypeFromSizesWithoutHiddenBit;

import com.google.auto.value.AutoValue;
import com.google.common.base.Preconditions;
import com.google.errorprone.annotations.Immutable;
import com.google.errorprone.annotations.InlineMe;
import java.math.BigInteger;
import java.util.BitSet;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

/**
 * Represents a floating-point number with customizable precision, consisting of sign, exponent, and
 * mantissa components.
 */
@Immutable
@AutoValue
public abstract class FloatingPointNumber {

  // TODO: remove deprecated constants from public API after 6.0 release (and delete the unused).
  @Deprecated(since = "6.0", forRemoval = true)
  public static final int SINGLE_PRECISION_EXPONENT_SIZE = 8;

  /**
   * @deprecated this constant can be confusing, as the SMTLIB2 standard expects the mantissa to
   *     include the hidden bit, but this constant does not.
   */
  @Deprecated(since = "6.0", forRemoval = true)
  public static final int SINGLE_PRECISION_MANTISSA_SIZE = 23;

  protected static final int SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT = 23;

  @Deprecated(since = "6.0", forRemoval = true)
  public static final int DOUBLE_PRECISION_EXPONENT_SIZE = 11;

  /**
   * @deprecated this constant can be confusing, as the SMTLIB2 standard expects the mantissa to
   *     include the hidden bit, but this constant does not.
   */
  @Deprecated(since = "6.0", forRemoval = true)
  public static final int DOUBLE_PRECISION_MANTISSA_SIZE = 52;

  protected static final int DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT = 52;

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

  /** Returns the {@link FloatingPointType} of this {@link FloatingPointNumber}. */
  public abstract FloatingPointType getFloatingPointType();

  public int getExponentSize() {
    return getFloatingPointType().getExponentSize();
  }

  /**
   * Returns the size of the mantissa (also called a coefficient or significand), excluding the sign
   * bit.
   *
   * @deprecated this method can be confusing, as the SMTLIB2 standard expects the mantissa to
   *     include the hidden bit, but this does not. Use {@link #getMantissaSizeWithoutHiddenBit()}
   *     instead if you want the mantissa without the hidden bit, and {@link
   *     #getMantissaSizeWithHiddenBit()} if you want it to include the hidden bit.
   */
  @Deprecated(since = "6.0", forRemoval = true)
  @SuppressWarnings("InlineMeSuggester")
  public final int getMantissaSize() {
    return getMantissaSizeWithoutHiddenBit();
  }

  /**
   * Returns the size of the mantissa (also called a coefficient or significand), excluding the
   * hidden bit.
   */
  public int getMantissaSizeWithoutHiddenBit() {
    return getFloatingPointType().getMantissaSizeWithoutHiddenBit();
  }

  /**
   * Returns the size of the mantissa (also called a coefficient or significand), including the
   * hidden bit.
   */
  public int getMantissaSizeWithHiddenBit() {
    return getFloatingPointType().getMantissaSizeWithHiddenBit();
  }

  /**
   * Returns the size of the precision as defined by the SMTLIB2 standard, i.e. sign bit + the size
   * of the exponent + the size of the mantissa (excluding the hidden bit).
   */
  public int getTotalSize() {
    return 1 + getMantissaSizeWithoutHiddenBit() + getExponentSize();
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
   * @param mantissaSizeWithoutHiddenBit the (maximum) size of the mantissa in bits (excluding the
   *     hidden bit)
   * @deprecated Use {@link #of(Sign, BigInteger, BigInteger, FloatingPointType)} instead.
   */
  @Deprecated(
      since = "2025.01, because using a boolean flag as signBit is misleading",
      forRemoval = true)
  @SuppressWarnings("InlineMeSuggester")
  public static FloatingPointNumber of(
      boolean sign,
      BigInteger exponent,
      BigInteger mantissa,
      int exponentSize,
      int mantissaSizeWithoutHiddenBit) {
    checkNotNull(exponent);
    checkNotNull(mantissa);
    return of(
        Sign.of(sign),
        exponent,
        mantissa,
        getFloatingPointTypeFromSizesWithoutHiddenBit(exponentSize, mantissaSizeWithoutHiddenBit));
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
   * @param mantissaSizeWithoutHiddenBit the (maximum) size of the mantissa in bits (excluding the
   *     hidden bit)
   * @deprecated Use {@link #of(Sign, BigInteger, BigInteger, FloatingPointType)} instead.
   */
  @Deprecated(
      since = "2026.01, because mantissa arguments with/without sign bits can be misleading",
      forRemoval = true)
  @SuppressWarnings("InlineMeSuggester")
  public static FloatingPointNumber of(
      Sign sign,
      BigInteger exponent,
      BigInteger mantissa,
      int exponentSize,
      int mantissaSizeWithoutHiddenBit) {
    checkNotNull(sign);
    checkNotNull(exponent);
    checkNotNull(mantissa);
    return of(
        sign,
        exponent,
        mantissa,
        getFloatingPointTypeFromSizesWithoutHiddenBit(exponentSize, mantissaSizeWithoutHiddenBit));
  }

  /**
   * Get a floating-point number with the given sign, exponent, and mantissa.
   *
   * @param sign the sign of the floating-point number.
   * @param exponent the exponent of the floating-point number, given as unsigned (not negative)
   *     number, including a bias of 2^(exponent size - 1) - 1.
   * @param mantissa the mantissa of the floating-point number, given as unsigned (not negative)
   *     number without hidden bit.
   * @param floatingPointType {@link FloatingPointType} to use. Mantissa and exponent sizes are used
   *     based on this type.
   */
  public static FloatingPointNumber of(
      Sign sign, BigInteger exponent, BigInteger mantissa, FloatingPointType floatingPointType) {
    Preconditions.checkArgument(exponent.signum() >= 0, "Exponent must not be negative");
    Preconditions.checkArgument(mantissa.signum() >= 0, "Mantissa must not be negative");
    Preconditions.checkArgument(
        exponent.bitLength() <= floatingPointType.getExponentSize(),
        "Exponent is too large for the exponent size");
    Preconditions.checkArgument(
        mantissa.bitLength() <= floatingPointType.getMantissaSizeWithoutHiddenBit(),
        "Mantissa is too large for the mantissa size");
    return new AutoValue_FloatingPointNumber(sign, exponent, mantissa, floatingPointType);
  }

  /**
   * Get a floating-point number encoded as bitvector as defined by IEEE 754.
   *
   * @param bits the bit-representation of the floating-point number, consisting of sign bit,
   *     exponent (without bias) and mantissa (without hidden bit) in this exact ordering
   * @param exponentSize the size of the exponent in bits.
   * @param mantissaSizeWithoutHiddenBit the size of the mantissa in bits (excluding the hidden bit)
   * @deprecated Use {@link #of(String, FloatingPointType)} instead.
   */
  @Deprecated(
      since = "2026.01, because mantissa arguments with/without sign bits can be misleading",
      forRemoval = true)
  @SuppressWarnings("InlineMeSuggester")
  public static FloatingPointNumber of(
      String bits, int exponentSize, int mantissaSizeWithoutHiddenBit) {
    checkNotNull(bits);
    return of(
        bits,
        getFloatingPointTypeFromSizesWithoutHiddenBit(exponentSize, mantissaSizeWithoutHiddenBit));
  }

  /**
   * Get a floating-point number encoded as bitvector as defined by IEEE 754.
   *
   * @param bits the bit-representation of the floating-point number, consisting of sign bit,
   *     exponent (without bias) and mantissa (without hidden bit) in this exact ordering.
   * @param floatingPointType {@link FloatingPointType} to use. Mantissa and exponent sizes are used
   *     based on this type.
   */
  public static FloatingPointNumber of(String bits, FloatingPointType floatingPointType) {
    // Note: sign bit + exponent size + mantissa size without hidden bit == exponent size + mantissa
    // size with hidden bit
    var exponentSize = floatingPointType.getExponentSize();
    var mantissaSizeWithoutHiddenBit = floatingPointType.getMantissaSizeWithoutHiddenBit();
    Preconditions.checkArgument(exponentSize >= 0, "Exponent size must not be negative");
    Preconditions.checkArgument(
        mantissaSizeWithoutHiddenBit >= 0, "Mantissa size must not be negative");
    Preconditions.checkArgument(
        bits.length() == floatingPointType.getTotalSize(),
        "Bitsize (%s) of floating point numeral does not match the size of sign, exponent and "
            + "mantissa (%s + %s + %s).",
        bits.length(),
        1,
        exponentSize,
        floatingPointType.getMantissaSizeWithoutHiddenBit());
    Preconditions.checkArgument(bits.chars().allMatch(c -> c == '0' || c == '1'));
    Sign sign = Sign.of(bits.charAt(0) == '1');
    BigInteger exponent = new BigInteger(bits.substring(1, 1 + exponentSize), 2);
    BigInteger mantissa =
        new BigInteger(
            bits.substring(1 + exponentSize, 1 + exponentSize + mantissaSizeWithoutHiddenBit), 2);
    return of(sign, exponent, mantissa, floatingPointType);
  }

  /**
   * Returns true if this floating-point number is an IEEE-754-2008 single precision type with 32
   * bits total length consisting of the sign bit, an 8 bit exponent, and a 23 bit mantissa
   * (excluding the hidden bit).
   *
   * @return true for IEEE-754 single precision type, false otherwise.
   */
  public boolean isIEEE754SinglePrecision() {
    return getTotalSize()
            == SINGLE_PRECISION_EXPONENT_SIZE
                + SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT
                + 1
        && getExponentSize() == SINGLE_PRECISION_EXPONENT_SIZE
        && getMantissaSizeWithoutHiddenBit() == SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT;
  }

  /**
   * Returns true if this floating-point number is an IEEE-754-2008 double precision type with 64
   * bits total length, consisting of the sign bit, an 11 bit exponent, and a 52 bit mantissa
   * (excluding the hidden bit).
   *
   * @return true for IEEE-754 double precision type, false otherwise.
   */
  public boolean isIEEE754DoublePrecision() {
    return getTotalSize()
            == DOUBLE_PRECISION_EXPONENT_SIZE
                + DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT
                + 1
        && getExponentSize() == DOUBLE_PRECISION_EXPONENT_SIZE
        && getMantissaSizeWithoutHiddenBit() == DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT;
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
    var mantissaSizeWithoutHiddenBit = getMantissaSizeWithoutHiddenBit();
    var exponentSize = getExponentSize();
    var mantissa = getMantissa();
    var exponent = getExponent();
    var bits = new BitSet(getTotalSize());
    if (getMathSign().isNegative()) {
      bits.set(exponentSize + mantissaSizeWithoutHiddenBit); // if negative, set first bit to 1
    }
    for (int i = 0; i < exponentSize; i++) {
      bits.set(mantissaSizeWithoutHiddenBit + i, exponent.testBit(i));
    }
    for (int i = 0; i < mantissaSizeWithoutHiddenBit; i++) {
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
    var length = getTotalSize();
    var str = new StringBuilder(length);
    var bits = getBits();
    for (int i = 0; i < length; i++) {
      str.append(bits.get(i) ? '1' : '0');
    }
    return str.reverse().toString();
  }
}
