// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/** Manager for dealing with formulas of the bitvector sort. */
public interface BitvectorFormulaManager {

  /**
   * Convert a number into a bitvector with given size.
   *
   * @throws IllegalArgumentException if the number is out of range for the given length.
   */
  BitvectorFormula makeBitvector(int length, long pI);

  /**
   * Convert a number into a bitvector with given size.
   *
   * @throws IllegalArgumentException if the number is out of range for the given length.
   */
  BitvectorFormula makeBitvector(int length, BigInteger pI);

  /**
   * Convert/Cast/Interpret a numeral formula into a bitvector with given size.
   *
   * <p>If the numeral formula is too large for the given length, we cut off the largest bits and
   * only use the least significant bits.
   */
  BitvectorFormula makeBitvector(int length, IntegerFormula pI);

  /** Convert/Cast/Interpret a signed/unsigned bitvector formula as an integer formula. */
  IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed);

  /**
   * Creates a variable with exactly the given name and bitwidth.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  BitvectorFormula makeVariable(int length, String pVar);

  /**
   * @see #makeVariable(int, String)
   */
  BitvectorFormula makeVariable(BitvectorType type, String pVar);

  /** This method returns the length of a bitvector, also denoted as bit-size. */
  int getLength(BitvectorFormula number);

  // Numeric Operations

  /**
   * This method returns the negated number, i.e., it is multiplied by "-1". The given number is
   * interpreted as signed bitvector and corresponds to "2^BITSIZE - number". The result has the
   * same length as the given number.
   */
  BitvectorFormula negate(BitvectorFormula number);

  /**
   * This method returns the addition of the given bitvectors. The result has the same length as the
   * given parameters. There can be an overflow, i.e., as one would expect from bitvector logic.
   * There is no difference in signed and unsigned numbers.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @return {@code number1 + number2}
   */
  BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2);

  /**
   * This method returns the subtraction of the given bitvectors. The result has the same length as
   * the given parameters. There can be an overflow, i.e., as one would expect from bitvector logic.
   * There is no difference in signed and unsigned numbers.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @return {@code number1 - number2}
   */
  BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2);

  /**
   * This method returns the division for two bitvector formulas.
   *
   * <p>For signed bitvectors, the result is rounded towards zero (also called "truncated integer
   * division", similar to the division in the C99 standard), e.g., a user can assume the following
   * equations:
   *
   * <ul>
   *   <li>10 / 5 = 2
   *   <li>10 / 3 = 3
   *   <li>10 / (-3) = -3
   *   <li>-10 / 5 = -2
   *   <li>-10 / 3 = -3
   *   <li>-10 / (-3) = 3
   * </ul>
   *
   * <p>If the divisor evaluates to zero (division-by-zero), either directly as value or indirectly
   * via an additional constraint, then the result of the division is defined as:
   *
   * <ul>
   *   <li>"-1" interpreted as bitvector (i.e., all bits set to "1"), if the dividend is
   *       non-negative, and
   *   <li>"1" interpreted as bitvector (i.e., all bits set to "0", except the last bit), if the
   *       dividend is negative.
   * </ul>
   *
   * <p>We refer to the SMTLIB standard version 2.6 for the division operator in BV theory for
   * additional information.
   *
   * @param dividend dividend of the operation.
   * @param divisor divisor of the operation.
   * @param signed whether to interpret all operands as signed or as unsigned numbers.
   */
  BitvectorFormula divide(BitvectorFormula dividend, BitvectorFormula divisor, boolean signed);

  /**
   * Deprecated and unsupported operation.
   *
   * <p>Returns the remainder of the given bitvectors and behaves equally to {@link
   * #remainder(BitvectorFormula, BitvectorFormula, boolean)}.
   *
   * <p>Deprecated in favor of remainder() and smodulo() due to confusing method naming and
   * inconsistent behavior (for signed modulo, the sign of the result follows the divisor, but for
   * signed remainder() it follows the dividend). Unsigned remainder() is equivalent to unsigned
   * modulo().
   */
  @Deprecated(
      forRemoval = true,
      since = "2024.08, because of inconsistent behavior at modulo and remainder operations")
  default BitvectorFormula modulo(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    return remainder(dividend, divisor, signed);
  }

  /**
   * This method returns the two complement signed remainder (smodulo(dividend, divisor) ==
   * remainder) for the Euclidean division (dividend = quotient * divisor + remainder) of two
   * bitvector formulas, with the sign of the remainder following the sign of the divisor.
   *
   * <p>The sign of the result follows the sign of the divisor; i.e. the quotient calculated in the
   * modulo operation is rounded in such a way that the result of the smodulo operation follows the
   * sign of the divisor. A user can assume the following example equations, with bitvectors
   * interpreted as signed decimal numbers, to hold:
   *
   * <ul>
   *   <li>smodulo(10, 5) == 0
   *   <li>smodulo(10, 3) == 1
   *   <li>smodulo(10, -3) == -2
   *   <li>smodulo(-10, 5) == 0
   *   <li>smodulo(-10, 3) == 2
   *   <li>smodulo(-10, -3) == -1
   * </ul>
   *
   * <p>If the divisor evaluates to zero (modulo-by-zero), either directly as value or indirectly
   * via an additional constraint, then the result of the modulo operation is defined as the
   * dividend itself. We refer to the SMTLIB standard version 2.6 for the division and remainder
   * operators in BV theory.
   *
   * <p>For unsigned modulo, we refer to the unsigned remainder method {@link
   * #remainder(BitvectorFormula, BitvectorFormula, boolean)}.
   *
   * <p>We refer to the SMTLIB standard version 2.6 for the smodulo operator in BV theory for
   * additional information.
   *
   * @param dividend dividend of the operation.
   * @param divisor divisor of the operation.
   */
  BitvectorFormula smodulo(BitvectorFormula dividend, BitvectorFormula divisor);

  /**
   * This method returns the remainder (remainder(dividend, divisor) == remainder) for the Euclidean
   * division (dividend = quotient * divisor + remainder) of two bitvector formulas.
   *
   * <p>For unsigned bitvectors, this returns the remainder of unsigned bitvector division.
   *
   * <p>For signed bitvectors, the sign of the result follows the sign of the dividend, i.e. the
   * quotient of the division is rounded in such a way that the sign of the result of the remainder
   * operation follows the sign of the dividend. A user can assume the following example equations,
   * with bitvectors interpreted as signed decimal numbers, to hold:
   *
   * <ul>
   *   <li>remainder(10, 5, true) == 0
   *   <li>remainder(10, 3, true) == 1
   *   <li>remainder(10, -3, true) == 1
   *   <li>remainder(-10, 5, true) == 0
   *   <li>remainder(-10, 3, true) == -1
   *   <li>remainder(-10, -3, true) == -1
   * </ul>
   *
   * <p>If the divisor evaluates to zero (modulo-by-zero), either directly as value or indirectly
   * via an additional constraint, then the result of the modulo operation is defined as the
   * dividend itself. We refer to the SMTLIB standard version 2.6 for the division and remainder
   * operators in BV theory.
   *
   * <p>We refer to the SMTLIB standard version 2.6 for the remainder operator in BV theory for
   * additional information.
   *
   * @param dividend dividend of the operation. The hidden bit is carried over from this bitvector
   *     for signed operations.
   * @param divisor divisor of the operation.
   * @param signed whether to interpret all operands as signed or as unsigned numbers.
   */
  BitvectorFormula remainder(BitvectorFormula dividend, BitvectorFormula divisor, boolean signed);

  /**
   * This method returns the multiplication of the given bitvectors. The result has the same length
   * as the given parameters. There can be an overflow, i.e., as one would expect from bitvector
   * logic. There is no difference in signed and unsigned numbers.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @return {@code number1 - number2}
   */
  BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2);

  // ----------------- Numeric relations -----------------

  /**
   * This method returns the bit-wise equality of the given bitvectors.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @return {@code number1 == number2}
   */
  BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2);

  /**
   * Compare the given bitvectors.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @param signed interpret the bitvectors as signed numbers instead of unsigned numbers
   * @return {@code number1 > number2}
   */
  BooleanFormula greaterThan(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  /**
   * Compare the given bitvectors.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @param signed interpret the bitvectors as signed numbers instead of unsigned numbers
   * @return {@code number1 >= number2}
   */
  BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  /**
   * Compare the given bitvectors.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @param signed interpret the bitvectors as signed numbers instead of unsigned numbers
   * @return {@code number1 < number2}
   */
  BooleanFormula lessThan(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  /**
   * Compare the given bitvectors.
   *
   * @param number1 a Formula
   * @param number2 a Formula
   * @param signed interpret the bitvectors as signed numbers instead of unsigned numbers
   * @return {@code number1 <= number2}
   */
  BooleanFormula lessOrEquals(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  // Bitvector operations

  /**
   * This method returns the bit-wise complement of the given bitvector.
   *
   * @param bits Formula
   * @return {@code ~bits}
   */
  BitvectorFormula not(BitvectorFormula bits);

  /**
   * This method returns the bit-wise AND of the given bitvectors.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 & bits2}
   */
  BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2);

  /**
   * This method returns the bit-wise OR of the given bitvectors.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 | bits2}
   */
  BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2);

  /**
   * This method returns the bit-wise XOR of the given bitvectors.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 ^ bits2}
   */
  BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2);

  /**
   * This method returns a term representing the right shift (towards least-significant bit) of
   * number by toShift. The result has the same length as the given number. On the left side, we
   * fill up the most significant bits with ones (i.e., arithmetic shift), if the number is signed
   * and negative, else we fill up with zeroes. For "toShift &gt;= bitsize", we return a bitvector
   * with value zero, if number was zero or positive, or all bits set to one, if negative.
   */
  BitvectorFormula shiftRight(BitvectorFormula number, BitvectorFormula toShift, boolean signed);

  /**
   * This method returns a term representing the left shift (towards most-significant bit) of number
   * by toShift. The result has the same length as the given number. On the right side, we fill up
   * the least significant bits with zeroes. For "toShift &gt;= bitsize", we return a bitvector with
   * value zero.
   */
  BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift);

  /**
   * This method returns a term representing the left rotation (towards most-significant bit) of
   * number by toRotate. The result has the same length as the given number. For "toRotate % bitsize
   * == 0", we return the number itself.
   *
   * @param toRotate the number of bits to be moved
   */
  BitvectorFormula rotateLeft(BitvectorFormula number, int toRotate);

  /**
   * This method returns a term representing the left rotation (towards most-significant bit) of
   * number by toRotate. The result has the same length as the given number. For "toRotate % bitsize
   * == 0", we return the number itself.
   *
   * @param toRotate unsigned bitvector, represents the number of bits to be moved
   */
  BitvectorFormula rotateLeft(BitvectorFormula number, BitvectorFormula toRotate);

  /**
   * This method returns a term representing the right rotation (towards least-significant bit) of
   * number by toRotate. The result has the same length as the given number. For "toRotate % bitsize
   * == 0", we return the number itself.
   *
   * @param toRotate the number of bits to be moved
   */
  BitvectorFormula rotateRight(BitvectorFormula number, int toRotate);

  /**
   * This method returns a term representing the right rotation (towards least-significant bit) of
   * number by toRotate. The result has the same length as the given number. For "toRotate % bitsize
   * == 0", we return the number itself.
   *
   * @param toRotate unsigned bitvector, represents the number of bits to be moved
   */
  BitvectorFormula rotateRight(BitvectorFormula number, BitvectorFormula toRotate);

  /** Concatenate two bitvectors. */
  BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix);

  /**
   * Extract a range of bits from a bitvector. We require {@code 0 <= lsb <= msb < bitsize}.
   *
   * <p>If msb equals lsb, then a single bit will be returned, i.e., the bit from the given
   * position. If lsb equals 0 and msb equals bitsize-1, then the complete bitvector will be
   * returned.
   *
   * @param number from where the bits are extracted.
   * @param msb Upper index for the most significant bit. Must be in interval from lsb to bitsize-1.
   * @param lsb Lower index for the least significant bit. Must be in interval from 0 to msb.
   * @param signed unused and will be removed in the future.
   */
  @Deprecated(forRemoval = true, since = "2022.04, because of unused flag for sign")
  default BitvectorFormula extract(BitvectorFormula number, int msb, int lsb, boolean signed) {
    return extract(number, msb, lsb);
  }

  /**
   * Extract a range of bits from a bitvector. We require {@code 0 <= lsb <= msb < bitsize}.
   *
   * <p>If msb equals lsb, then a single bit will be returned, i.e., the bit from the given
   * position. If lsb equals 0 and msb equals bitsize-1, then the complete bitvector will be
   * returned.
   *
   * @param number from where the bits are extracted.
   * @param msb Upper index for the most significant bit. Must be in interval from lsb to bitsize-1.
   * @param lsb Lower index for the least significant bit. Must be in interval from 0 to msb.
   */
  BitvectorFormula extract(BitvectorFormula number, int msb, int lsb);

  /**
   * Extend a bitvector to the left (add most significant bits). If signed is set and the given
   * number is negative, then the bit "1" will be added several times, else "0".
   *
   * @param number The bitvector to extend.
   * @param extensionBits How many bits to add.
   * @param signed Whether the extension should depend on the hidden bit.
   */
  BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed);

  /** All given bitvectors are pairwise unequal. */
  BooleanFormula distinct(List<BitvectorFormula> pBits);

  default BooleanFormula distinct(BitvectorFormula... pBits) {
    return distinct(List.of(pBits));
  }
}
