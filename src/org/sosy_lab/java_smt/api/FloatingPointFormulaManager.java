// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import static org.sosy_lab.java_smt.api.FormulaType.getFloatingPointType;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager.BitvectorFormulaAndBooleanFormula;

/**
 * Floating point operations.
 *
 * <p>Most operations are overloaded: there is an option of either using the default rounding mode
 * (set via the option {@code solver.floatingPointRoundingMode}), or providing the rounding mode
 * explicitly.
 *
 * <p>If the result of an operation can not be exactly represented by the available floating-point
 * type, i.e., the given precision is insufficient, the result is rounded to the nearest possible
 * floating-point representation, depending on the given rounding mode.
 *
 * <p>Example: If the input number is too large to be represented as a floating point with the given
 * type, it will be converted to positive infinity (+inf) or negative infinity (-inf). If the input
 * number is too small to be represented with the given type (closer to zero than the smallest
 * possible floating-point number), it will be converted to zero, with the sign preserved.
 */
public interface FloatingPointFormulaManager {

  /**
   * Creates a floating point formula representing the given double value with the specified type.
   */
  FloatingPointFormula makeNumber(double n, FloatingPointType type);

  /**
   * Creates a floating point formula representing the given double value with the specified type
   * and rounding mode.
   */
  FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Creates a floating point formula representing the given BigDecimal value with the specified
   * type.
   */
  FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type);

  /**
   * Creates a floating point formula representing the given BigDecimal value with the specified
   * type and rounding mode.
   */
  FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Creates a floating point formula representing the given string value with the specified type.
   *
   * <p>The string can be any valid floating-point number, e.g., "1.0", "1.0e-3", but also special
   * values like "NaN", "Infinity", or "-0.0", etc. A leading "+" sign or "-" sign is allowed.
   */
  FloatingPointFormula makeNumber(String n, FloatingPointType type);

  /**
   * Creates a floating point formula representing the given string value with the specified type
   * and rounding mode.
   *
   * <p>The string can be any valid floating-point number, e.g., "1.0", "1.0e-3", but also special
   * values like "NaN", "Infinity", or "-0.0", etc. A leading "+" sign or "-" sign is allowed.
   */
  FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Creates a floating point formula representing the given Rational value with the specified type.
   */
  FloatingPointFormula makeNumber(Rational n, FloatingPointType type);

  /**
   * Creates a floating point formula representing the given Rational value with the specified type
   * and rounding mode.
   */
  FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Creates a floating point formula from the given {@link FloatingPointNumber}.
   *
   * @param number the floating point number
   */
  default FloatingPointFormula makeNumber(FloatingPointNumber number) {
    return makeNumber(
        number.getExponent(),
        number.getMantissa(),
        number.getMathSign(),
        getFloatingPointType(number.getExponentSize(), number.getMantissaSize()));
  }

  /**
   * Creates a floating point formula from the given exponent, mantissa, and sign-bit with the
   * specified type.
   *
   * @param exponent the exponent part of the floating point number
   * @param mantissa the mantissa part of the floating point number
   * @param signBit the sign bit of the floating point number, e.g., true for negative numbers
   */
  @Deprecated(
      since = "2025.01, because using a boolean flag as signBit is misleading",
      forRemoval = true)
  default FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, boolean signBit, FloatingPointType type) {
    return makeNumber(exponent, mantissa, Sign.of(signBit), type);
  }

  /**
   * Creates a floating point formula from the given exponent, mantissa, and sign with the specified
   * type.
   *
   * @param exponent the exponent part of the floating point number
   * @param mantissa the mantissa part of the floating point number
   * @param sign the sign of the floating point number
   */
  FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type);

  /**
   * Creates a variable with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  FloatingPointFormula makeVariable(String pVar, FloatingPointType type);

  FloatingPointFormula makePlusInfinity(FloatingPointType type);

  FloatingPointFormula makeMinusInfinity(FloatingPointType type);

  FloatingPointFormula makeNaN(FloatingPointType type);

  /**
   * Build a formula of compatible type from a {@link FloatingPointFormula}. This method uses the
   * default rounding mode.
   *
   * <p>Compatible formula types are all numeral types and bitvector types. It is also possible to
   * cast a floating-point number into another floating-point type. We do not support casting from
   * boolean or array types. We try to keep an exact representation, however fall back to rounding
   * if needed.
   *
   * @param source the source formula of floating-point type
   * @param targetType the type of the resulting formula
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link
   *     FloatingPointFormula} cannot be cast to {@link BooleanFormula}.
   */
  @Deprecated(
      forRemoval = true,
      since = "2022.06, because of missing sign-bit for bitvector conversion")
  default <T extends Formula> T castTo(FloatingPointFormula source, FormulaType<T> targetType) {
    return castTo(source, true, targetType);
  }

  /**
   * Build a formula of compatible type from a {@link FloatingPointFormula}.
   *
   * <p>Compatible formula types are all numeral types and bitvector types. It is also possible to
   * cast a floating-point number into another floating-point type. We do not support casting from
   * boolean or array types. We try to keep an exact representation, however fall back to rounding
   * if needed.
   *
   * @param source the source formula of floating-point type
   * @param targetType the type of the resulting formula
   * @param pFloatingPointRoundingMode if rounding is needed, we apply the rounding mode.
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link
   *     FloatingPointFormula} cannot be cast to {@link BooleanFormula}.
   */
  @Deprecated(
      forRemoval = true,
      since = "2022.06, because of missing sign-bit for bitvector conversion")
  default <T extends Formula> T castTo(
      FloatingPointFormula source,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return castTo(source, true, targetType, pFloatingPointRoundingMode);
  }

  /**
   * Build a formula of compatible type from a {@link FloatingPointFormula}. This method uses the
   * default rounding mode.
   *
   * <p>Compatible formula types are all numeral types and (signed/unsigned) bitvector types. It is
   * also possible to cast a floating-point number into another floating-point type. We do not
   * support casting from boolean or array types. We try to keep an exact representation, however
   * fall back to rounding if needed.
   *
   * @param source the source formula of floating-point type
   * @param signed if a {@link BitvectorFormula} is given as target, we additionally use this flag.
   *     Otherwise, we ignore it.
   * @param targetType the type of the resulting formula
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link
   *     FloatingPointFormula} cannot be cast to {@link BooleanFormula}.
   */
  <T extends Formula> T castTo(
      FloatingPointFormula source, boolean signed, FormulaType<T> targetType);

  /**
   * Build a formula of compatible type from a {@link FloatingPointFormula}.
   *
   * <p>Compatible formula types are all numeral types and (signed/unsigned) bitvector types. It is
   * also possible to cast a floating-point number into another floating-point type. We do not
   * support casting from boolean or array types. We try to keep an exact representation, however
   * fall back to rounding if needed.
   *
   * @param source the source formula of floating-point type
   * @param signed if a {@link BitvectorFormula} is given as target, we additionally use this flag.
   *     Otherwise, we ignore it.
   * @param targetType the type of the resulting formula
   * @param pFloatingPointRoundingMode if rounding is needed, we apply the rounding mode.
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link
   *     FloatingPointFormula} cannot be cast to {@link BooleanFormula}.
   */
  <T extends Formula> T castTo(
      FloatingPointFormula source,
      boolean signed,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Build a {@link FloatingPointFormula} from another compatible formula. This method uses the
   * default rounding mode.
   *
   * <p>Compatible formula types are all numeral types and (signed/unsigned) bitvector types. It is
   * also possible to cast a floating-point number into another floating-point type. We do not
   * support casting from boolean or array types. We try to keep an exact representation, however
   * fall back to rounding if needed.
   *
   * @param source the source formula of compatible type
   * @param signed if a {@link BitvectorFormula} is given as source, we additionally use this flag.
   *     Otherwise, we ignore it.
   * @param targetType the type of the resulting formula
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link BooleanFormula}
   *     cannot be cast to {@link FloatingPointFormula}.
   */
  FloatingPointFormula castFrom(Formula source, boolean signed, FloatingPointType targetType);

  /**
   * Build a {@link FloatingPointFormula} from another compatible formula.
   *
   * <p>Compatible formula types are all numeral types and (signed/unsigned) bitvector types. It is
   * also possible to cast a floating-point number into another floating-point type. We do not
   * support casting from boolean or array types. We try to keep an exact representation, however
   * fall back to rounding if needed.
   *
   * @param source the source formula of compatible type
   * @param signed if a {@link BitvectorFormula} is given as source, we additionally use this flag.
   *     Otherwise, we ignore it.
   * @param targetType the type of the resulting formula
   * @param pFloatingPointRoundingMode if rounding is needed, we apply the rounding mode.
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link BooleanFormula}
   *     cannot be cast to {@link FloatingPointFormula}.
   */
  FloatingPointFormula castFrom(
      Formula source,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Create a formula that interprets the given bitvector as a floating-point value in the IEEE
   * format, according to the given type. The sum of the sizes of exponent and mantissa of the
   * target type plus 1 (for the sign bit) needs to be equal to the size of the bitvector.
   *
   * <p>Note: This method will return a value that is (numerically) far away from the original
   * value. This method is completely different from {@link #castFrom}, which will produce a
   * floating-point value close to the numeral value.
   */
  FloatingPointFormula fromIeeeBitvector(BitvectorFormula number, FloatingPointType pTargetType);

  /**
   * Create a formula that produces a representation of the given floating-point value as a
   * bitvector conforming to the IEEE 754-2008 format. The size of the resulting bitvector is the
   * sum of the sizes of the exponent and mantissa of the input formula plus 1 (for the sign bit).
   */
  BitvectorFormula toIeeeBitvector(FloatingPointFormula number);

  /**
   * Create a formula that produces a representation of the given floating-point value as a
   * bitvector conforming to the IEEE 754-2008 format. The size of the resulting bitvector is the
   * sum of the sizes of the exponent and mantissa of the input formula plus 1 (for the sign bit).
   * This implementation can be used independently of {@link
   * #toIeeeBitvector(FloatingPointFormula)}, as it does not rely on an SMT solvers support for
   * {@link #toIeeeBitvector(FloatingPointFormula)}. Behavior for special FP values (NaN, Inf, etc.)
   * is not defined, and returned values are solver dependent. In case you want to define how to
   * handle those values, please use {@link #toIeeeBitvector(FloatingPointFormula, String, Map)}.
   * This method is based on a suggestion in the SMTLib2 standard ( <a
   * href="https://smt-lib.org/theories-FloatingPoint.shtml">source</a>) implementation:
   *
   * <p>(declare-fun b () (_ BitVec m))
   *
   * <p>(assert (= ((_ to_fp eb sb) b) f))
   *
   * @param number the {@link FloatingPointFormula} to be converted into an IEEE bitvector.
   * @param bitvectorConstantName the name of the returned {@link BitvectorFormula}.
   * @return {@link BitvectorFormulaAndBooleanFormula} consisting of the transformed input
   *     floating-point as a {@link BitvectorFormula} and the additional constraint as {@link
   *     BooleanFormula}.
   */
  BitvectorFormulaAndBooleanFormula toIeeeBitvector(
      FloatingPointFormula number, String bitvectorConstantName);

  /**
   * Create a formula that produces a representation of the given floating-point value as a
   * bitvector conforming to the IEEE 754-2008 format. The size of the resulting bitvector is the
   * sum of the sizes of the exponent and mantissa of the input formula plus 1 (for the sign bit).
   * This implementation can be used independently of {@link
   * #toIeeeBitvector(FloatingPointFormula)}, as it does not rely on an SMT solvers support for
   * {@link #toIeeeBitvector(FloatingPointFormula)}. Behavior for special FP values (NaN, Inf, etc.)
   * can be defined using the specialFPConstantHandling parameter. This method is based on a
   * suggestion in the SMTLib2 standard ( <a
   * href="https://smt-lib.org/theories-FloatingPoint.shtml">source</a>) implementation:
   *
   * <p>(declare-fun b () (_ BitVec m))
   *
   * <p>(assert (= ((_ to_fp eb sb) b) f))
   *
   * @param number the {@link FloatingPointFormula} to be converted into an IEEE bitvector.
   * @param bitvectorConstantName the name of the returned {@link BitvectorFormula}.
   * @param specialFPConstantHandling a {@link Map} defining the returned {@link BitvectorFormula}
   *     for special {@link FloatingPointFormula} constant numbers. You are only allowed to specify
   *     a mapping for special FP numbers with more than one well-defined bitvector representation,
   *     i.e. NaN and +/- Infinity. The width of the mapped bitvector values has to match the
   *     expected width of the bitvector return value. The {@link FloatingPointType}, i.e.
   *     precision, of the key FP numbers has to match the {@link FloatingPointType} of the
   *     parameter {@code number}. For an empty {@link Map}, or missing mappings, this method
   *     behaves like {@link #toIeeeBitvector(FloatingPointFormula, String)}.
   * @return {@link BitvectorFormulaAndBooleanFormula} consisting of the transformed input
   *     floating-point as a {@link BitvectorFormula} and the additional constraint as {@link
   *     BooleanFormula}.
   */
  BitvectorFormulaAndBooleanFormula toIeeeBitvector(
      FloatingPointFormula number,
      String bitvectorConstantName,
      Map<FloatingPointFormula, BitvectorFormula> specialFPConstantHandling);

  FloatingPointFormula round(FloatingPointFormula formula, FloatingPointRoundingMode roundingMode);

  // ----------------- Arithmetic relations, return type NumeralFormula -----------------

  FloatingPointFormula negate(FloatingPointFormula number);

  FloatingPointFormula abs(FloatingPointFormula number);

  /**
   * Returns the maximum value of the two given floating-point numbers. If one of the numbers is
   * NaN, the other number is returned.
   */
  FloatingPointFormula max(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Returns the minimum value of the two given floating-point numbers. If one of the numbers is
   * NaN, the other number is returned.
   */
  FloatingPointFormula min(FloatingPointFormula number1, FloatingPointFormula number2);

  FloatingPointFormula sqrt(FloatingPointFormula number);

  FloatingPointFormula sqrt(FloatingPointFormula number, FloatingPointRoundingMode roundingMode);

  FloatingPointFormula add(FloatingPointFormula number1, FloatingPointFormula number2);

  FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  FloatingPointFormula subtract(FloatingPointFormula number1, FloatingPointFormula number2);

  FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  FloatingPointFormula divide(FloatingPointFormula number1, FloatingPointFormula number2);

  FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  FloatingPointFormula multiply(FloatingPointFormula number1, FloatingPointFormula number2);

  FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * remainder: x - y * n, where n in Z is nearest to x/y. The result can be negative even for two
   * positive arguments, e.g. "rem(5, 4) == 1" and "rem(5, 6) == -1", as opposed to integer modulo
   * operators.
   */
  FloatingPointFormula remainder(FloatingPointFormula dividend, FloatingPointFormula divisor);

  // ----------------- Numeric relations, return type BooleanFormula -----------------

  /**
   * Create a term for assigning one floating-point term to another. This means both terms are
   * considered equal afterward, based on their bit pattern (i.e., <code>0.0 != -0
   * .0</code> and <code>NaN ==/!= NaN</code>, depending on the bit pattern of each NaN). This
   * method is the same as the method <code>equal</code> for other theories.
   */
  BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Create a term for comparing the equality of two floating-point terms, according to standard
   * floating-point semantics (i.e., <code>NaN != NaN</code> and <code>0.0 == -0.0</code>). Be
   * careful to not use this method when you really need {@link #assignment(FloatingPointFormula,
   * FloatingPointFormula)}.
   */
  BooleanFormula equalWithFPSemantics(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Returns whether an FP number is greater than another FP number. If one of the numbers is NaN,
   * the result is always false.
   */
  BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Returns whether an FP number is greater or equal than another FP number. If one of the numbers
   * is NaN, the result is always false.
   */
  BooleanFormula greaterOrEquals(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Returns whether an FP number is less than another FP number. If one of the numbers is NaN, the
   * result is always false.
   */
  BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Returns whether an FP number is less or equal than another FP number. If one of the numbers is
   * NaN, the result is always false.
   */
  BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Check whether a floating-point number is NaN.
   *
   * <p>The bit patterns for NaN in SMTLIB are identical to IEEE 754:
   *
   * <ul>
   *   <li>sign=? (irrelevant for NaN)
   *   <li>exponent=11...11 (all bits are 1)
   *   <li>mantissa!=00...00 (mantissa is not all 0)
   * </ul>
   */
  BooleanFormula isNaN(FloatingPointFormula number);

  /**
   * Checks whether a formula is positive or negative infinity.
   *
   * <p>The bit patterns for infinity in SMTLIB are identical to IEEE 754:
   *
   * <ul>
   *   <li>sign=? (0 for +Inf, 1 for -Inf)
   *   <li>exponent=11...11 (all bits are 1)
   *   <li>mantissa=00...00 (all bits are 0)
   * </ul>
   */
  BooleanFormula isInfinity(FloatingPointFormula number);

  /**
   * Checks whether a formula is positive or negative zero.
   *
   * <p>The bit patterns for zero in SMTLIB are identical to IEEE 754:
   *
   * <ul>
   *   <li>sign=? (0 for +0, 1 for -0)
   *   <li>exponent=00...00 (all bits are 0)
   *   <li>mantissa=00...00 (all bits are 0)
   * </ul>
   */
  BooleanFormula isZero(FloatingPointFormula number);

  /**
   * Checks whether a formula is normal FP number.
   *
   * <p>The bit patterns for normal FP numbers in SMTLIB are identical to IEEE 754:
   *
   * <ul>
   *   <li>sign=? (0 for positive numbers, 1 for negative numbers)
   *   <li>exponent!=00...00 and exponent!=11...11 (exponent is not all 0 or all 1)
   *   <li>mantissa=? (mantissa is irrelevant)
   * </ul>
   */
  BooleanFormula isNormal(FloatingPointFormula number);

  /**
   * Checks whether a formula is subnormal FP number.
   *
   * <p>The bit patterns for subnormal FP numbers in SMTLIB are identical to IEEE 754:
   *
   * <ul>
   *   <li>sign=? (0 for positive numbers, 1 for negative numbers)
   *   <li>exponent=00...00 (exponent is all 0)
   *   <li>mantissa!=00...00 (mantissa is not all 0)
   * </ul>
   */
  BooleanFormula isSubnormal(FloatingPointFormula number);

  /**
   * Checks whether a formula is negative, including -0.0.
   *
   * <p>The bit patterns for negative FP numbers in SMTLIB are identical to IEEE 754:
   *
   * <ul>
   *   <li>sign=1 (1 for negative numbers)
   *   <li>number is not NaN, i.e., exponent=11...11 implies mantissa=00...00
   * </ul>
   */
  BooleanFormula isNegative(FloatingPointFormula number);

  /**
   * Returns the size of the mantissa (also called a coefficient or significant), including the
   * sign bit, for the given {@link FloatingPointFormula}.
   */
  int getMantissaSize(FloatingPointFormula number);

  /**
   * Returns the size of the exponent for the given {@link FloatingPointFormula}.
   */
  int getExponentSize(FloatingPointFormula number);
}
