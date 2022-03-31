// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
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
   * Convert/Cast a numeral formula into a bitvector with given size.
   *
   * <p>If the numeral formula is too large for the given length, we cut off the largest bits and
   * only use the smallest bits.
   */
  BitvectorFormula makeBitvector(int length, IntegerFormula pI);

  /** Interpret a signed/unsigned bitvector formula as an integer formula. */
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

  int getLength(BitvectorFormula number);

  // Numeric Operations

  BitvectorFormula negate(BitvectorFormula number);

  BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2);

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
   * @param number1 dividend, numerator
   * @param number2 divisor, denumerator
   * @param signed whether to interpret all operands as signed or as unsigned numbers.
   */
  BitvectorFormula divide(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  /**
   * This method returns the remainder (modulo) for two bitvector formulas.
   *
   * <p>For signed bitvectors, the sign of the result follows the sign of the numerator, e.g., a
   * user can assume the following equations:
   *
   * <ul>
   *   <li>10 % 5 = 0
   *   <li>10 % 3 = 1
   *   <li>10 % (-3) = 1
   *   <li>-10 % 5 = 0
   *   <li>-10 % 3 = -1
   *   <li>-10 % (-3) = -1
   * </ul>
   *
   * @param number1 dividend, numerator
   * @param number2 divisor, denumerator
   * @param signed whether to interpret all operands as signed or as unsigned numbers.
   */
  BitvectorFormula modulo(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2);

  // ----------------- Numeric relations -----------------

  BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2);

  BooleanFormula greaterThan(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  BooleanFormula lessThan(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  BooleanFormula lessOrEquals(BitvectorFormula number1, BitvectorFormula number2, boolean signed);

  // Bitvector operations

  /**
   * Creates a formula representing a negation of the argument.
   *
   * @param bits Formula
   * @return {@code !f1}
   */
  BitvectorFormula not(BitvectorFormula bits);

  /**
   * Creates a formula representing an AND of the two arguments.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code f1 & f2}
   */
  BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2);

  /**
   * Creates a formula representing an OR of the two arguments.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code f1 | f2}
   */
  BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2);

  BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2);

  /**
   * Return a term representing the (arithmetic if signed is true) right shift of number by toShift.
   */
  BitvectorFormula shiftRight(BitvectorFormula number, BitvectorFormula toShift, boolean signed);

  BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift);

  BitvectorFormula concat(BitvectorFormula number, BitvectorFormula append);

  /**
   * @param number The bitvector to extract.
   * @param msb Upper index. Must be greater than or equal to 0 and less than the bit-width of
   *     number.
   * @param lsb Lower index. Must be less than or equal to msb and greater or equal to 0.
   * @param signed Whether the extension should depend on the sign bit. Note: Some SMT-Solvers
   *     ignore this. (i.e. Boolector)
   */
  BitvectorFormula extract(BitvectorFormula number, int msb, int lsb, boolean signed);

  /**
   * Extend a bitvector to the left (add most significant bits).
   *
   * @param number The bitvector to extend.
   * @param extensionBits How many bits to add.
   * @param signed Whether the extension should depend on the sign bit.
   */
  BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed);

  /** All given bitvectors are pairwise unequal. */
  BooleanFormula distinct(List<BitvectorFormula> pBits);
}
