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
package org.sosy_lab.java_smt.api;

import java.math.BigDecimal;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

/**
 * Floating point operations.
 *
 * <p>Most operations are overloaded: there is an option of either using the default rounding mode
 * (set via the option {@code solver.floatingPointRoundingMode}), or providing the rounding mode
 * explicitly.
 */
public interface FloatingPointFormulaManager {

  FloatingPointFormula makeNumber(double n, FloatingPointType type);

  FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  FloatingPointFormula makeNumber(BigDecimal n, FloatingPointType type);

  FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  FloatingPointFormula makeNumber(String n, FloatingPointType type);

  FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

  FloatingPointFormula makeNumber(Rational n, FloatingPointType type);

  FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode);

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

  <T extends Formula> T castTo(FloatingPointFormula number, FormulaType<T> targetType);

  <T extends Formula> T castTo(
      FloatingPointFormula number,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  /**
   * Build a {@link FloatingPointFormula} from another compatible formula. This method uses the
   * default rounding mode.
   *
   * <p>Compatible formula types are all numeral types and bitvector types. It is also possible to
   * cast a floating-point number into another floating-point type. We do not support casting from
   * boolean or array types. We try to keep an exact representation, however fall back to rounding
   * if needed.
   *
   * @param source the source formula of compatible type
   * @param signed if a {@link BitvectorFormula} is given as source, we additionally use this flag.
   *     Otherwise we ignore it.
   * @param targetType the type of the resulting formula
   * @throws IllegalArgumentException if an incompatible type is used, e.g. a {@link BooleanFormula}
   *     cannot be cast to {@link FloatingPointFormula}.
   */
  FloatingPointFormula castFrom(Formula source, boolean signed, FloatingPointType targetType);

  /**
   * Build a {@link FloatingPointFormula} from another compatible formula.
   *
   * <p>Compatible formula types are all numeral types and bitvector types. It is also possible to
   * cast a floating-point number into another floating-point type. We do not support casting from
   * boolean or array types. We try to keep an exact representation, however fall back to rounding
   * if needed.
   *
   * @param source the source formula of compatible type
   * @param signed if a {@link BitvectorFormula} is given as source, we additionally use this flag.
   *     Otherwise we ignore it.
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
   * bitvector conforming to the IEEE format. The size of the resulting bitvector is the sum of the
   * sizes of the exponent and mantissa of the input formula plus 1 (for the sign bit).
   */
  BitvectorFormula toIeeeBitvector(FloatingPointFormula number);

  FloatingPointFormula round(FloatingPointFormula formula, FloatingPointRoundingMode roundingMode);

  // ----------------- Arithmetic relations, return type NumeralFormula -----------------

  FloatingPointFormula negate(FloatingPointFormula number);

  FloatingPointFormula abs(FloatingPointFormula number);

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

  // ----------------- Numeric relations, return type BooleanFormula -----------------

  /**
   * Create a term for assigning one floating-point term to another. This means both terms are
   * considered equal afterwards. This method is the same as the method <code>equal</code> for other
   * theories.
   */
  BooleanFormula assignment(FloatingPointFormula number1, FloatingPointFormula number2);

  /**
   * Create a term for comparing the equality of two floating-point terms, according to standard
   * floating-point semantics (i.e., NaN != NaN). Be careful to not use this method when you really
   * need {@link #assignment(FloatingPointFormula, FloatingPointFormula)}.
   */
  BooleanFormula equalWithFPSemantics(FloatingPointFormula number1, FloatingPointFormula number2);

  BooleanFormula greaterThan(FloatingPointFormula number1, FloatingPointFormula number2);

  BooleanFormula greaterOrEquals(FloatingPointFormula number1, FloatingPointFormula number2);

  BooleanFormula lessThan(FloatingPointFormula number1, FloatingPointFormula number2);

  BooleanFormula lessOrEquals(FloatingPointFormula number1, FloatingPointFormula number2);

  BooleanFormula isNaN(FloatingPointFormula number);

  BooleanFormula isInfinity(FloatingPointFormula number);

  BooleanFormula isZero(FloatingPointFormula number);

  BooleanFormula isNormal(FloatingPointFormula number);

  BooleanFormula isSubnormal(FloatingPointFormula number);

  /** checks whether a formula is negative, including -0.0. */
  BooleanFormula isNegative(FloatingPointFormula number);
}
